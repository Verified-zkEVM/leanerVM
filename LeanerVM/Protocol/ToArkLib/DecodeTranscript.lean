/-
  LeanerVM.Protocol.ToArkLib.DecodeTranscript

  The transcript of a protocol decoded round by round from a list of readings: at each round a
  slot reads the round's value off the front of the list, given the rounds before it. Decoders of
  appended schedules are built from decoders of their parts. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.KnowledgeAppend

/-!
# Decoding transcripts from readings

A run of a protocol may be recorded as a flat list of readings (the blocks a Fiat–Shamir chain
absorbed and squeezed, say) rather than as a transcript. A `Slot α β` reads a value of type `β` off
the front of a `List α` and returns the readings left. It consumes a prefix of the readings and
what it reads depends on that prefix alone (`Slot.read_iff`): readings after it pass through
(`Slot.read_append`) and can be taken away again (`Slot.read_of_read_append`). `Slot.pure`,
`Slot.next`, `Slot.take`, `Slot.map` and `Slot.bind` build slots. A `SlotDecoder α pSpec` gives, at
each round of `pSpec`, the slot that reads the round's value, from the transcript of the rounds
before it: a message may be decoded with a claim the earlier rounds leave. Then

* `run D i hi l`: the first `i` rounds read off `l`, with the readings left; `runFull D l`: all of
  them. A run consumes a prefix as a slot does (`run_eq_some_iff`, `run_append`,
  `run_of_run_append`);
* `decodeAt D i l`: the transcript of the first `i` rounds, if they read exactly `l`;
* `decode D l`: the full transcript, if it reads exactly `l`;
* `decodePrefix D l`: the longest prefix that reads exactly `l`, with its number of rounds. It
  includes every round after the input runs out whose slot reads nothing
  (`decodePrefix_eq_some_iff`), and is `none` when no prefix reads exactly `l`
  (`decodePrefix_eq_none_iff`).

`decodePrefix_mono`: readings appended to `l` only extend the prefix decoded from it.
`decode_eq_of_decodePrefix`: the full transcript decoded from `l ++ l'` begins with the prefix
decoded from `l`. `decodePrefix_of_run_append`: if `l ++ l'` decodes and its first `i` rounds read
exactly `l`, then `l` decodes to the full transcript's prefix of at least `i` rounds.

Decoders compose. `empty` decodes a schedule of no round, `single s` one of one round by the slot
`s` (`runFull_empty`, `runFull_single`). `append D₁ D₂` decodes `pSpec₁ ++ₚ pSpec₂`: the rounds
of `pSpec₁` by `D₁`, then those of `pSpec₂` by `D₂ t₁`, where `t₁` is the transcript of `pSpec₁`
read first. `runFull_append` and `decode_append` give its full decoding as the two in sequence;
`run_append_left` and `run_append_right` its partial runs, read through the projections
`Verifier.KnowledgeAppend.left`, `leftFull` and `right`. Decoders of the repository's schedules
of steps are in `LeanerVM.Protocol.ToArkLib.DecodeSteps`.
-/

namespace LeanerVM.Protocol

open ProtocolSpec

@[expose] public section

/-! ## Slots -/

/-- A value of type `β` read off the front of a list of readings, with the readings left. It
consumes a prefix of the readings, and what it reads depends on that prefix alone. -/
structure Slot (α β : Type) where
  /-- The value read off the front of the readings, and the readings left. -/
  read : List α → Option (β × List α)
  /-- The readings consumed are a prefix, which read alone gives the same value. -/
  read_iff : ∀ {l : List α} {x : β} {r : List α},
    read l = some (x, r) ↔ ∃ c, l = c ++ r ∧ read c = some (x, [])

namespace Slot

variable {α β γ : Type}

/-- Readings appended to the input are left after the value. -/
theorem read_append (s : Slot α β) {l : List α} {x : β} {r : List α}
    (h : s.read l = some (x, r)) (l' : List α) : s.read (l ++ l') = some (x, r ++ l') := by
  obtain ⟨c, rfl, hc⟩ := s.read_iff.mp h
  exact s.read_iff.mpr ⟨c, List.append_assoc c r l', hc⟩

/-- Readings appended to the input and left after the value may be taken away. -/
theorem read_of_read_append (s : Slot α β) {l l' : List α} {x : β} {r : List α}
    (h : s.read (l ++ l') = some (x, r ++ l')) : s.read l = some (x, r) := by
  obtain ⟨c, hc, hr⟩ := s.read_iff.mp h
  refine s.read_iff.mpr ⟨c, List.append_cancel_right (bs := l') ?_, hr⟩
  rw [hc, List.append_assoc]

/-- The value `x`, read off no reading. -/
def pure (x : β) : Slot α β where
  read l := some (x, l)
  read_iff {l y r} := by
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨fun ⟨hx, hr⟩ ↦ ⟨[], hr ▸ rfl, hx, rfl⟩, fun ⟨c, hl, hx, hc⟩ ↦ ⟨hx, by simp [hl, hc]⟩⟩

/-- One reading, through a partial map. -/
def next (f : α → Option β) : Slot α β where
  read
    | [] => none
    | a :: r => (f a).map (·, r)
  read_iff {l x r} := by
    constructor
    · intro h
      cases l with
      | nil => cases h
      | cons a l =>
        obtain ⟨y, hy, he⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ⟨[a], rfl, by simp [hy]⟩
    · rintro ⟨_ | ⟨a, _ | ⟨b, c⟩⟩, rfl, h⟩
      · cases h
      · simpa using h
      · simp at h

/-- `k` readings, through a partial map of the list of them. -/
def take (k : ℕ) (f : List α → Option β) : Slot α β where
  read l := if k ≤ l.length then (f (l.take k)).map (·, l.drop k) else none
  read_iff {l x r} := by
    constructor
    · intro h
      by_cases hk : k ≤ l.length
      · rw [ite_eq_left hk] at h
        obtain ⟨y, hy, he⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        refine ⟨l.take k, (List.take_append_drop k l).symm, ?_⟩
        rw [ite_eq_left (by simp; omega), List.take_take, Nat.min_self, hy,
          List.drop_eq_nil_of_le (by simp)]
        rfl
      · rw [ite_eq_right hk] at h
        cases h
    · rintro ⟨c, rfl, h⟩
      by_cases hk : k ≤ c.length
      · rw [ite_eq_left hk] at h
        obtain ⟨y, hy, he⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨rfl, hd⟩ := Prod.mk.inj he
        have hc : c.length = k := by
          have := List.length_drop (i := k) (l := c)
          rw [hd] at this
          simp at this
          omega
        rw [ite_eq_left (by simp; omega), List.take_append_of_le_length hk,
          List.drop_append_of_le_length hk, hd, hy]
        rfl
      · rw [ite_eq_right hk] at h
        cases h

/-- The value of `s`, mapped by `g`. -/
def map (g : β → γ) (s : Slot α β) : Slot α γ where
  read l := (s.read l).map fun p ↦ (g p.1, p.2)
  read_iff {l x r} := by
    simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨y, r', hy, rfl, rfl⟩
      obtain ⟨c, rfl, hc⟩ := s.read_iff.mp hy
      exact ⟨c, rfl, y, [], hc, rfl, rfl⟩
    · rintro ⟨c, rfl, y, r', hy, rfl, rfl⟩
      exact ⟨y, r, s.read_append hy r, rfl, rfl⟩

/-- The slot `s`, then the slot `f x` for the value `x` it read. -/
def bind (s : Slot α β) (f : β → Slot α γ) : Slot α γ where
  read l := (s.read l).bind fun p ↦ (f p.1).read p.2
  read_iff {l x r} := by
    simp only [Option.bind_eq_some_iff, Prod.exists]
    constructor
    · rintro ⟨y, r₁, hy, hf⟩
      obtain ⟨c₁, rfl, hc₁⟩ := s.read_iff.mp hy
      obtain ⟨c₂, rfl, hc₂⟩ := (f y).read_iff.mp hf
      exact ⟨c₁ ++ c₂, by rw [List.append_assoc], y, c₂, by simpa using s.read_append hc₁ c₂,
        hc₂⟩
    · rintro ⟨c, rfl, y, r₁, hy, hf⟩
      exact ⟨y, r₁ ++ r, s.read_append hy r, by simpa using (f y).read_append hf r⟩

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
private def whole {β : Type} : Option (β × List α) → Option β
  | some (x, []) => some x
  | _ => none

private theorem whole_eq_some {β : Type} {o : Option (β × List α)} {x : β} :
    whole o = some x ↔ o = some (x, []) := by
  rcases o with _ | ⟨y, _ | ⟨a, r⟩⟩ <;> simp [whole]

/-- The transcript of the first `i` rounds, if they read exactly `l`. -/
@[no_expose] def decodeAt (i : Fin (n + 1)) (l : List α) : Option (pSpec.Transcript i) :=
  whole (D.run i.val (by omega) l)

/-- The full transcript, if it reads exactly `l`. -/
@[no_expose] def decode (l : List α) : Option pSpec.FullTranscript := whole (D.runFull l)

/-- The run of the first `i` rounds, with the longest of them that reads exactly `l`: one pass,
each round's run extending the last. -/
private def scan (l : List α) : (i : ℕ) → (hi : i ≤ n) →
    Option (pSpec.Transcript ⟨i, by omega⟩ × List α) ×
      Option (Σ k : Fin (n + 1), pSpec.Transcript k)
  | 0, _ => (some (fun a ↦ a.elim0, l),
      (whole (some ((fun a ↦ a.elim0 : pSpec.Transcript ⟨0, by omega⟩), l))).map
        (⟨⟨0, by omega⟩, ·⟩))
  | i + 1, hi =>
    let s := scan l i (by omega)
    let r := s.1.bind fun p ↦
      ((D.slot ⟨i, hi⟩ p.1).read p.2).map fun q ↦ (Transcript.concat (m := ⟨i, hi⟩) q.1 p.1, q.2)
    (r, ((whole r).map (⟨⟨i + 1, by omega⟩, ·⟩)).or s.2)

/-- The longest prefix of the transcript that reads exactly `l`, with its number of rounds: it
includes every round after the input runs out whose slot reads nothing. -/
@[no_expose] def decodePrefix (l : List α) : Option (Σ i : Fin (n + 1), pSpec.Transcript i) :=
  (D.scan l n le_rfl).2

/-- The first `i` rounds read exactly `l` when their run leaves no reading. -/
theorem decodeAt_eq_some {i : Fin (n + 1)} {l : List α} {tr : pSpec.Transcript i} :
    D.decodeAt i l = some tr ↔ D.run i.val (by omega) l = some (tr, []) := whole_eq_some

/-- The full transcript reads exactly `l` when the full run leaves no reading. -/
theorem decode_eq_some {l : List α} {t : pSpec.FullTranscript} :
    D.decode l = some t ↔ D.runFull l = some (t, []) := whole_eq_some

/-- A run consumes a prefix of its input, which run alone gives the same transcript. -/
theorem run_eq_some_iff {i : ℕ} {hi : i ≤ n} {l : List α} {tr : pSpec.Transcript ⟨i, by omega⟩}
    {r : List α} :
    D.run i hi l = some (tr, r) ↔ ∃ c, l = c ++ r ∧ D.run i hi c = some (tr, []) := by
  induction i generalizing l r with
  | zero =>
    simp only [run, Option.some.injEq, Prod.mk.injEq]
    exact ⟨fun ⟨htr, hr⟩ ↦ ⟨[], by simp [hr], htr, rfl⟩,
      fun ⟨c, hl, htr, hc⟩ ↦ ⟨htr, by simp [hl, hc]⟩⟩
  | succ i ih =>
    simp only [run, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨t, s, hp, x, r', hq, rfl, rfl⟩
      obtain ⟨c₁, rfl, hc₁⟩ := (ih (hi := by omega)).mp hp
      obtain ⟨c₂, rfl, hc₂⟩ := (D.slot ⟨i, hi⟩ t).read_iff.mp hq
      exact ⟨c₁ ++ c₂, by rw [List.append_assoc], t, c₂,
        (ih (hi := by omega)).mpr ⟨c₁, rfl, hc₁⟩, x, [], hc₂, rfl, rfl⟩
    · rintro ⟨c, rfl, t, s, hp, x, r', hq, rfl, rfl⟩
      obtain ⟨c₁, rfl, hc₁⟩ := (ih (hi := by omega)).mp hp
      exact ⟨t, s ++ r, (ih (hi := by omega)).mpr ⟨c₁, by rw [List.append_assoc], hc₁⟩, x, r,
        by simpa using (D.slot ⟨i, hi⟩ t).read_append hq r, rfl, rfl⟩

/-- Readings appended to the input of a run are left after it. -/
theorem run_append {i : ℕ} {hi : i ≤ n} {l : List α} {tr : pSpec.Transcript ⟨i, by omega⟩}
    {r : List α} (h : D.run i hi l = some (tr, r)) (l' : List α) :
    D.run i hi (l ++ l') = some (tr, r ++ l') := by
  obtain ⟨c, rfl, hc⟩ := D.run_eq_some_iff.mp h
  exact D.run_eq_some_iff.mpr ⟨c, List.append_assoc c r l', hc⟩

/-- Readings appended to the input of a run and left after it may be taken away. -/
theorem run_of_run_append {i : ℕ} {hi : i ≤ n} {l l' : List α}
    {tr : pSpec.Transcript ⟨i, by omega⟩} {r : List α}
    (h : D.run i hi (l ++ l') = some (tr, r ++ l')) : D.run i hi l = some (tr, r) := by
  obtain ⟨c, hc, hr⟩ := D.run_eq_some_iff.mp h
  refine D.run_eq_some_iff.mpr ⟨c, List.append_cancel_right (bs := l') ?_, hr⟩
  rw [hc, List.append_assoc]

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

private theorem scan_fst (l : List α) (i : ℕ) (hi : i ≤ n) : (D.scan l i hi).1 = D.run i hi l := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show ((D.scan l i (by omega)).1.bind _) = _
    rw [ih (by omega)]
    rfl

private theorem scan_snd_eq_some_iff {l : List α} {k : ℕ} {hk : k ≤ n} {i : Fin (n + 1)}
    {tr : pSpec.Transcript i} :
    (D.scan l k hk).2 = some ⟨i, tr⟩ ↔
      i.val ≤ k ∧ D.decodeAt i l = some tr ∧
        ∀ j : Fin (n + 1), i < j → j.val ≤ k → D.decodeAt j l = none := by
  induction k with
  | zero =>
    show (D.decodeAt ⟨0, Nat.zero_lt_succ n⟩ l).map _ = _ ↔ _
    simp only [Option.map_eq_some_iff, Sigma.mk.inj_iff]
    constructor
    · rintro ⟨t, ht, rfl, he⟩
      obtain rfl := eq_of_heq he
      exact ⟨le_rfl, ht, fun j hj hj0 ↦ absurd (Fin.lt_def.mp hj) (by simp only; omega)⟩
    · rintro ⟨hi0, ht, -⟩
      obtain rfl : i = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext (Nat.le_zero.mp hi0)
      exact ⟨tr, ht, rfl, HEq.rfl⟩
  | succ k ih =>
    show ((whole ((D.scan l k (by omega)).1.bind _)).map _).or _ = _ ↔ _
    rw [scan_fst]
    change ((D.decodeAt ⟨k + 1, Nat.lt_succ_of_le hk⟩ l).map _).or _ = _ ↔ _
    simp only [Option.or_eq_some_iff, Option.map_eq_some_iff, Sigma.mk.inj_iff,
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

private theorem scan_snd_eq_none_iff {l : List α} {k : ℕ} {hk : k ≤ n} :
    (D.scan l k hk).2 = none ↔ ∀ i : Fin (n + 1), i.val ≤ k → D.decodeAt i l = none := by
  induction k with
  | zero =>
    show (D.decodeAt ⟨0, Nat.zero_lt_succ n⟩ l).map _ = none ↔ _
    rw [Option.map_eq_none_iff]
    exact ⟨fun h i hi ↦ (Fin.ext (Nat.le_zero.mp hi) : i = ⟨0, _⟩) ▸ h, fun h ↦ h _ le_rfl⟩
  | succ k ih =>
    show ((whole ((D.scan l k (by omega)).1.bind _)).map _).or _ = none ↔ _
    rw [scan_fst]
    change ((D.decodeAt ⟨k + 1, Nat.lt_succ_of_le hk⟩ l).map _).or _ = none ↔ _
    rw [Option.or_eq_none_iff, Option.map_eq_none_iff, ih]
    constructor
    · rintro ⟨hn, hlater⟩ i hi
      by_cases hik : i.val ≤ k
      · exact hlater i hik
      · obtain rfl : i = ⟨k + 1, Nat.lt_succ_of_le hk⟩ := Fin.ext (show i.val = k + 1 by omega)
        exact hn
    · exact fun h ↦ ⟨h _ le_rfl, fun i hi ↦ h i (by omega)⟩

/-- `decodePrefix l` is the longest prefix that reads exactly `l`: it includes every round after
the input runs out whose slot reads nothing. -/
theorem decodePrefix_eq_some_iff {l : List α} {i : Fin (n + 1)} {tr : pSpec.Transcript i} :
    D.decodePrefix l = some ⟨i, tr⟩ ↔
      D.decodeAt i l = some tr ∧ ∀ j : Fin (n + 1), i < j → D.decodeAt j l = none := by
  rw [decodePrefix, scan_snd_eq_some_iff]
  exact ⟨fun ⟨_, ht, hj⟩ ↦ ⟨ht, fun j h ↦ hj j h (by omega)⟩,
    fun ⟨ht, hj⟩ ↦ ⟨by omega, ht, fun j h _ ↦ hj j h⟩⟩

/-- `decodePrefix l` is `none` exactly when no prefix reads exactly `l`. -/
theorem decodePrefix_eq_none_iff {l : List α} :
    D.decodePrefix l = none ↔ ∀ i : Fin (n + 1), D.decodeAt i l = none := by
  rw [decodePrefix, scan_snd_eq_none_iff]
  exact ⟨fun h i ↦ h i (by omega), fun h i _ ↦ h i⟩

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
    obtain rfl : l' = [] :=
      (List.append_eq_nil_iff.mp (Prod.mk.inj (Option.some.inj hs')).2.symm).2
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

/-- **A cut where a round begins**: if `l ++ l'` decodes to `t` and its first `i` rounds read
exactly `l`, then `l` decodes to the prefix of `t` of some `j ≥ i` rounds. -/
theorem decodePrefix_of_run_append {l l' : List α} {t : pSpec.FullTranscript} {i : ℕ}
    {hi : i ≤ n} {tr : pSpec.Transcript ⟨i, by omega⟩} (ht : D.decode (l ++ l') = some t)
    (hr : D.run i hi (l ++ l') = some (tr, l')) :
    ∃ j : Fin (n + 1), i ≤ j.val ∧
      D.decodePrefix l = some ⟨j, FullTranscript.take j.val j.is_le t⟩ := by
  have hl : D.decodeAt ⟨i, by omega⟩ l = some tr :=
    D.decodeAt_eq_some.mpr (D.run_of_run_append (r := []) (by simpa using hr))
  cases hp : D.decodePrefix l with
  | none => exact absurd ((D.decodePrefix_eq_none_iff.mp hp) ⟨i, by omega⟩) (by rw [hl]; simp)
  | some p =>
    obtain ⟨j, tr'⟩ := p
    have hj := (D.decodePrefix_eq_some_iff.mp hp).2
    refine ⟨j, not_lt.mp fun hji ↦ ?_, ?_⟩
    · have := hj ⟨i, by omega⟩ (Fin.lt_def.mpr hji)
      simp [hl] at this
    · rw [D.decode_eq_of_decodePrefix ht hp]

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

end SlotDecoder

/-! ## Appended schedules -/

section Append

variable {α : Type} {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- The rounds of `pSpec₁` in a transcript of `pSpec₁ ++ₚ pSpec₂` that has passed them, as a full
transcript of `pSpec₁`: `left` at the seam, typed as a full transcript. -/
def Verifier.KnowledgeAppend.leftFull {k : Fin (m + n + 1)}
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k) (h : m ≤ k.val) : pSpec₁.FullTranscript :=
  left tr (Fin.last m) h

namespace SlotDecoder

open Verifier.KnowledgeAppend

/-- The decoder of `pSpec₁ ++ₚ pSpec₂`: the rounds of `pSpec₁` by `D₁`, then those of `pSpec₂` by
`D₂ t₁`, where `t₁` is the transcript of `pSpec₁` read first. -/
def append (D₁ : SlotDecoder α pSpec₁) (D₂ : pSpec₁.FullTranscript → SlotDecoder α pSpec₂) :
    SlotDecoder α (pSpec₁ ++ₚ pSpec₂) where
  slot := Fin.addCases (motive := fun k ↦
      (pSpec₁ ++ₚ pSpec₂).Transcript k.castSucc → Slot α ((pSpec₁ ++ₚ pSpec₂).«Type» k))
    (fun i tr ↦ (D₁.slot i (left tr i.castSucc (by simp))).map
      (cast (append_Type_castAdd (pSpec₂ := pSpec₂) i).symm))
    (fun j tr ↦ ((D₂ (leftFull tr (by simp))).slot j (right tr j.castSucc (by simp))).map
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
      ((D₂ (leftFull tr (Nat.le_add_right m j))).slot ⟨j, hj⟩ (right tr ⟨j, by omega⟩ le_rfl)).map
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
    ((D₁.append D₂).run m (by omega) l).map (fun p ↦ (leftFull p.1 le_rfl, p.2)) =
      D₁.runFull l :=
  run_append_left D₁ D₂ m le_rfl l

private theorem run_append_right_aux (j : ℕ) (hj : j ≤ n) (l : List α) (i : ℕ) (hi : i ≤ m + n)
    (hij : i = m + j) :
    ((D₁.append D₂).run i hi l).map
        (fun p ↦ (leftFull p.1 (by simp only; omega), right p.1 ⟨j, by omega⟩ (by simp only; omega),
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
      cases hq : ((D₂ (leftFull p.1 (Nat.le_add_right m j))).slot ⟨j, by omega⟩
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
on what it left, read through `leftFull` and `right`. -/
theorem run_append_right (j : ℕ) (hj : j ≤ n) (l : List α) :
    ((D₁.append D₂).run (m + j) (by omega) l).map
        (fun p ↦ (leftFull p.1 (Nat.le_add_right m j), right p.1 ⟨j, by omega⟩ le_rfl, p.2)) =
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

end SlotDecoder

end Append

end

end LeanerVM.Protocol
