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
    · rcases l with _ | ⟨a, l⟩
      · nofun
      · intro h
        obtain ⟨y, hy, ⟨⟩⟩ := Option.map_eq_some_iff.mp h
        exact ⟨[a], rfl, by simp [hy]⟩
    · rintro ⟨_ | ⟨a, _ | ⟨b, c⟩⟩, rfl, h⟩ <;> simp_all

/-- `k` readings, through a partial map of the list of them. -/
def take (k : ℕ) (f : List α → Option β) : Slot α β where
  read l := if k ≤ l.length then (f (l.take k)).map (·, l.drop k) else none
  read_iff {l x r} := by
    constructor
    · intro h
      split_ifs at h with hk
      obtain ⟨y, hy, ⟨⟩⟩ := Option.map_eq_some_iff.mp h
      exact ⟨l.take k, (List.take_append_drop k l).symm, by simp [hk, List.take_take, hy]⟩
    · rintro ⟨c, rfl, h⟩
      split_ifs at h with hk
      obtain ⟨y, hy, he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, hd⟩ := Prod.mk.inj he
      have hc : c.length = k := by have := List.drop_eq_nil_iff.mp hd; omega
      simp [hc, hy, List.take_append_of_le_length hk, List.drop_append_of_le_length hk, hd]

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
  obtain ⟨⟨j, tr'⟩, hp⟩ := (Option.ne_none_iff_exists' (o := D.decodePrefix l)).mp
    fun hp ↦ by simp [(D.decodePrefix_eq_none_iff.mp hp) ⟨i, by omega⟩] at hl
  obtain rfl := D.decode_eq_of_decodePrefix ht hp
  refine ⟨j, not_lt.mp fun hji ↦ ?_, hp⟩
  simp [(D.decodePrefix_eq_some_iff.mp hp).2 ⟨i, by omega⟩ (Fin.lt_def.mpr hji)] at hl

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

/-- A round of the first schedule is read by the first decoder's slot. -/
theorem append_slot_left (i : ℕ) (hi : i < m) (h : i < m + n)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ⟨i, by omega⟩) :
    (D₁.append D₂).slot ⟨i, h⟩ tr = (D₁.slot ⟨i, hi⟩ (left tr ⟨i, by omega⟩ le_rfl)).map
      (cast (append_Type_castAdd (pSpec₂ := pSpec₂) ⟨i, hi⟩).symm) := by
  dsimp only [append]
  exact congrFun (Fin.addCases_left (motive := fun k ↦
    (pSpec₁ ++ₚ pSpec₂).Transcript k.castSucc → Slot α ((pSpec₁ ++ₚ pSpec₂).«Type» k)) ⟨i, hi⟩) tr

/-- A round of the second schedule is read by the second decoder's slot. -/
theorem append_slot_right (j : ℕ) (hj : j < n) (h : m + j < m + n)
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
  | zero => exact congrArg some (Prod.ext (funext fun a ↦ a.elim0) rfl)
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
      rw [← hl]
      exact congrArg some (Prod.ext rfl (Prod.ext (funext fun a ↦ a.elim0) rfl))
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

/-! ## Slots as a monad -/

namespace Slot

variable {α β γ δ ε : Type}

/-- The slot that reads nothing: it fails on every input. -/
def fail : Slot α β where
  read _ := none
  read_iff := by simp

/-- Two slots that read alike are equal. -/
theorem ext {s t : Slot α β} (h : ∀ l, s.read l = t.read l) : s = t := by
  rcases s with ⟨r, _⟩
  rcases t with ⟨r', _⟩
  obtain rfl : r = r' := funext h
  rfl

/-- Slots are a monad: `pure` reads nothing, `bind` reads one slot, then the next. -/
instance : Monad (Slot α) where
  pure := Slot.pure
  bind := Slot.bind

@[simp] theorem read_pure (x : β) (l : List α) :
    (Pure.pure x : Slot α β).read l = some (x, l) := rfl

@[simp] theorem read_bind (s : Slot α β) (f : β → Slot α γ) (l : List α) :
    (s >>= f).read l = (s.read l).bind fun p ↦ (f p.1).read p.2 := rfl

@[simp] theorem read_fail (l : List α) : (fail : Slot α β).read l = none := rfl

@[simp] theorem read_next_nil (f : α → Option β) : (next f).read [] = none := rfl

@[simp] theorem read_next_cons (f : α → Option β) (a : α) (r : List α) :
    (next f).read (a :: r) = (f a).map (·, r) := rfl

@[simp] theorem read_mapM (g : β → γ) (s : Slot α β) (l : List α) :
    (g <$> s).read l = (s.read l).map fun p ↦ (g p.1, p.2) := by
  show (s.read l).bind _ = _
  cases s.read l <;> rfl

instance : LawfulMonad (Slot α) := LawfulMonad.mk'
  (id_map := fun s ↦ ext fun l ↦ by
    show (s.read l).bind _ = _
    rcases s.read l with _ | ⟨x, r⟩ <;> rfl)
  (pure_bind := fun _ _ ↦ ext fun _ ↦ rfl)
  (bind_assoc := fun s f g ↦ ext fun l ↦ by
    show ((s.read l).bind _).bind _ = (s.read l).bind _
    rcases s.read l with _ | ⟨x, r⟩ <;> rfl)

/-! ## Slots that read alike -/

/-- `t` reads wherever `s` reads: the same prefix, with a value related to `s`'s by `R`. -/
def Refines (R : β → γ → Prop) (s : Slot α β) (t : Slot α γ) : Prop :=
  ∀ l x r, s.read l = some (x, r) → ∃ y, t.read l = some (y, r) ∧ R x y

/-- `s` and `t` read alike: on every input both fail, or both read the same prefix, with values
related by `R`. -/
def Agree (R : β → γ → Prop) (s : Slot α β) (t : Slot α γ) : Prop :=
  Refines R s t ∧ Refines (flip R) t s

theorem Refines.refl (s : Slot α β) : Refines Eq s s := fun _ x _ h ↦ ⟨x, h, rfl⟩

theorem Refines.mono {R R' : β → γ → Prop} {s : Slot α β} {t : Slot α γ} (h : Refines R s t)
    (hR : ∀ x y, R x y → R' x y) : Refines R' s t := fun l x r hs ↦
  (h l x r hs).imp fun _ ⟨ht, hxy⟩ ↦ ⟨ht, hR _ _ hxy⟩

theorem Refines.pure {R : β → γ → Prop} {x : β} {y : γ} (h : R x y) :
    Refines R (Pure.pure x : Slot α β) (Pure.pure y) := by
  rintro l x' r ⟨⟩
  exact ⟨y, rfl, h⟩

theorem Refines.bind {R : β → γ → Prop} {R' : δ → ε → Prop} {s : Slot α β} {t : Slot α γ}
    {f : β → Slot α δ} {g : γ → Slot α ε} (h : Refines R s t)
    (hf : ∀ x y, R x y → Refines R' (f x) (g y)) : Refines R' (s >>= f) (t >>= g) := by
  intro l z r hs
  rw [read_bind, Option.bind_eq_some_iff] at hs
  obtain ⟨⟨x, l₁⟩, hx, hz⟩ := hs
  obtain ⟨y, hy, hxy⟩ := h l x l₁ hx
  obtain ⟨w, hw, hzw⟩ := hf x y hxy l₁ z r hz
  exact ⟨w, by rw [read_bind, hy, Option.bind_some, hw], hzw⟩

theorem Refines.map {R : β → γ → Prop} {s : Slot α β} {t : Slot α γ} (h : Refines R s t)
    (f : β → δ) (g : γ → ε) :
    Refines (fun x y ↦ ∃ a b, R a b ∧ x = f a ∧ y = g b) (f <$> s) (g <$> t) := by
  intro l z r hs
  rw [read_mapM, Option.map_eq_some_iff] at hs
  obtain ⟨⟨x, r'⟩, hx, he⟩ := hs
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  obtain ⟨y, hy, hxy⟩ := h l x r' hx
  exact ⟨g y, by rw [read_mapM, hy]; rfl, x, y, hxy, rfl, rfl⟩

theorem Agree.refl (s : Slot α β) : Agree Eq s s :=
  ⟨Refines.refl s, (Refines.refl s).mono fun _ _ h ↦ h.symm⟩

theorem Agree.mono {R R' : β → γ → Prop} {s : Slot α β} {t : Slot α γ} (h : Agree R s t)
    (hR : ∀ x y, R x y → R' x y) : Agree R' s t :=
  ⟨h.1.mono hR, h.2.mono fun x y h ↦ hR y x h⟩

theorem Agree.pure {R : β → γ → Prop} {x : β} {y : γ} (h : R x y) :
    Agree R (Pure.pure x : Slot α β) (Pure.pure y) :=
  ⟨Refines.pure h, Refines.pure (R := flip R) h⟩

theorem Agree.bind {R : β → γ → Prop} {R' : δ → ε → Prop} {s : Slot α β} {t : Slot α γ}
    {f : β → Slot α δ} {g : γ → Slot α ε} (h : Agree R s t)
    (hf : ∀ x y, R x y → Agree R' (f x) (g y)) : Agree R' (s >>= f) (t >>= g) :=
  ⟨h.1.bind fun x y hxy ↦ (hf x y hxy).1, h.2.bind fun y x hxy ↦ (hf x y hxy).2⟩

/-- Two slots that read alike, their values mapped, still read alike: a map of the values changes
no reading. -/
theorem Agree.map {R : β → γ → Prop} {s : Slot α β} {t : Slot α γ} (h : Agree R s t)
    (f : β → δ) (g : γ → ε) : Agree (fun _ _ ↦ True) (s.map f) (t.map g) := by
  have hm : ∀ {β' δ' : Type} (u : Slot α β') (k : β' → δ'), u.map k = k <$> u :=
    fun u k ↦ ext fun l ↦ by rw [read_mapM]; rfl
  rw [hm, hm]
  exact ⟨(h.1.map f g).mono fun _ _ _ ↦ trivial, (h.2.map g f).mono fun _ _ _ ↦ trivial⟩

end Slot

/-! ## Decoders that read alike -/

namespace SlotDecoder

variable {α : Type}

section Alike

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- Two decoders of one schedule read alike: at every round, whatever the rounds before it, their
slots read the same prefix of every input, or both fail. Their values may differ. -/
def ReadsAlike (D D' : SlotDecoder α pSpec) : Prop :=
  ∀ k tr tr', Slot.Agree (fun _ _ ↦ True) (D.slot k tr) (D'.slot k tr')

variable {D D' : SlotDecoder α pSpec}

/-- Decoders that read alike leave the same readings after every run, or both fail. -/
theorem ReadsAlike.run (h : ReadsAlike D D') (i : ℕ) (hi : i ≤ n) (l : List α) :
    (D.run i hi l).map Prod.snd = (D'.run i hi l).map Prod.snd := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have ih := ih (by omega)
    simp only [SlotDecoder.run]
    cases ho : D.run i (by omega) l with
    | none =>
      rw [ho, Option.map_none, eq_comm, Option.map_eq_none_iff] at ih
      rw [ih]
      rfl
    | some p =>
      rw [ho, Option.map_some, eq_comm, Option.map_eq_some_iff] at ih
      obtain ⟨p', hp', hr⟩ := ih
      rw [hp', Option.bind_some, Option.bind_some, Option.map_map, Option.map_map]
      have hag := h ⟨i, hi⟩ p.1 p'.1
      rw [hr]
      cases hq : (D.slot ⟨i, hi⟩ p.1).read p.2 with
      | none =>
        cases hq' : (D'.slot ⟨i, hi⟩ p'.1).read p.2 with
        | none => rfl
        | some q' =>
          obtain ⟨_, hq'', -⟩ := hag.2 p.2 q'.1 q'.2 (by rw [hq'])
          rw [hq] at hq''
          cases hq''
      | some q =>
        obtain ⟨y, hq', -⟩ := hag.1 p.2 q.1 q.2 (by rw [hq])
        rw [hq']
        rfl

/-- Decoders that read alike decode the same number of rounds off every input. -/
theorem ReadsAlike.decodePrefix (h : ReadsAlike D D') (l : List α) :
    (D.decodePrefix l).map Sigma.fst = (D'.decodePrefix l).map Sigma.fst := by
  have hat : ∀ (E E' : SlotDecoder α pSpec), ReadsAlike E E' → ∀ i : Fin (n + 1),
      (E.decodeAt i l).isSome → (E'.decodeAt i l).isSome := by
    intro E E' hE i hs
    obtain ⟨tr, htr⟩ := Option.isSome_iff_exists.mp hs
    have hr := hE.run i.val (by omega) l
    rw [E.decodeAt_eq_some.mp htr, Option.map_some, eq_comm, Option.map_eq_some_iff] at hr
    obtain ⟨⟨tr', r⟩, hr', rfl⟩ := hr
    exact Option.isSome_iff_exists.mpr ⟨tr', E'.decodeAt_eq_some.mpr hr'⟩
  have hsymm : ReadsAlike D' D := fun k tr tr' ↦ ⟨(h k tr' tr).2, (h k tr' tr).1⟩
  have hiff : ∀ i : Fin (n + 1), (D.decodeAt i l).isSome ↔ (D'.decodeAt i l).isSome :=
    fun i ↦ ⟨hat D D' h i, hat D' D hsymm i⟩
  have key : ∀ (E E' : SlotDecoder α pSpec), (∀ i : Fin (n + 1),
      (E.decodeAt i l).isSome ↔ (E'.decodeAt i l).isSome) → ∀ i tr,
      E.decodePrefix l = some ⟨i, tr⟩ → ∃ tr', E'.decodePrefix l = some ⟨i, tr'⟩ := by
    intro E E' hE i tr hp
    obtain ⟨ht, hj⟩ := E.decodePrefix_eq_some_iff.mp hp
    obtain ⟨tr', ht'⟩ := Option.isSome_iff_exists.mp ((hE i).mp (by rw [ht]; rfl))
    refine ⟨tr', E'.decodePrefix_eq_some_iff.mpr ⟨ht', fun j hij ↦ ?_⟩⟩
    have := hj j hij
    exact Option.not_isSome_iff_eq_none.mp fun hs ↦ by
      rw [← hE j, this] at hs
      exact absurd hs (by simp)
  cases hD : D.decodePrefix l with
  | none =>
    cases hD' : D'.decodePrefix l with
    | none => rfl
    | some p =>
      obtain ⟨tr, htr⟩ := key D' D (fun i ↦ (hiff i).symm) p.1 p.2 hD'
      rw [hD] at htr
      cases htr
  | some p =>
    obtain ⟨tr', htr'⟩ := key D D' hiff p.1 p.2 hD
    rw [htr']
    rfl

/-- **Decodability does not depend on the values read**: decoders that read alike decode some
prefix of the same inputs. -/
theorem ReadsAlike.isSome_decodePrefix (h : ReadsAlike D D') (l : List α) :
    (D.decodePrefix l).isSome = (D'.decodePrefix l).isSome := by
  have := h.decodePrefix l
  cases hD : D.decodePrefix l <;> cases hD' : D'.decodePrefix l <;> simp_all

/-- Decoders of no round read alike. -/
theorem readsAlike_empty {pSpec : ProtocolSpec 0} :
    ReadsAlike (empty : SlotDecoder α pSpec) empty := fun k ↦ k.elim0

/-- Decoders of one round read alike when their slots do. -/
theorem readsAlike_single {pSpec : ProtocolSpec 1} {s s' : Slot α (pSpec.«Type» 0)}
    (h : Slot.Agree (fun _ _ ↦ True) s s') : ReadsAlike (single s) (single s') := by
  rintro ⟨k, hk⟩ _ _
  obtain rfl : k = 0 := by omega
  exact h

end Alike

section AppendAlike

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Appended decoders read alike when their parts do, whatever the first part read. -/
theorem readsAlike_append {D₁ D₁' : SlotDecoder α pSpec₁}
    {D₂ D₂' : pSpec₁.FullTranscript → SlotDecoder α pSpec₂} (h₁ : ReadsAlike D₁ D₁')
    (h₂ : ∀ t t', ReadsAlike (D₂ t) (D₂' t')) : ReadsAlike (D₁.append D₂) (D₁'.append D₂') := by
  rintro ⟨k, hk⟩ tr tr'
  by_cases hkm : k < m
  · rw [append_slot_left D₁ D₂ k hkm hk tr, append_slot_left D₁' D₂' k hkm hk tr']
    exact (h₁ _ _ _).map _ _
  · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
    rw [append_slot_right D₁ D₂ j (by omega) hk tr, append_slot_right D₁' D₂' j (by omega) hk tr']
    exact (h₂ _ _ _ _ _).map _ _

end AppendAlike

/-! ## A decoder as one slot -/

section ToSlot

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- Every round of a decoder, as one slot reading the full transcript. -/
def toSlot (D : SlotDecoder α pSpec) : Slot α pSpec.FullTranscript where
  read := D.runFull
  read_iff := D.run_eq_some_iff

@[simp] theorem read_toSlot (D : SlotDecoder α pSpec) (l : List α) :
    D.toSlot.read l = D.runFull l := rfl

/-- The transcript of a schedule of one round. -/
def oneTranscript {pSpec : ProtocolSpec 1} (x : pSpec.«Type» 0) : pSpec.FullTranscript
  | ⟨0, _⟩ => x

@[simp] theorem oneTranscript_zero {pSpec : ProtocolSpec 1} (x : pSpec.«Type» 0) :
    oneTranscript x 0 = x := rfl

/-- A decoder of one round is its slot. -/
theorem toSlot_single {pSpec : ProtocolSpec 1} (s : Slot α (pSpec.«Type» 0)) :
    (single s).toSlot = oneTranscript <$> s := by
  refine Slot.ext fun l ↦ ?_
  rw [read_toSlot, Slot.read_mapM]
  change Option.map _ (s.read l) = _
  congr 1
  funext p
  refine Prod.ext (funext fun i ↦ ?_) rfl
  obtain ⟨k, hk⟩ := i
  obtain rfl : k = 0 := by omega
  rfl

/-- A decoder of no round reads nothing. -/
theorem toSlot_empty {pSpec : ProtocolSpec 0} :
    (empty : SlotDecoder α pSpec).toSlot = pure fun i ↦ i.elim0 := rfl

variable {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **The append law as slots**: an appended decoder reads its first part, then its second. -/
theorem toSlot_append (D₁ : SlotDecoder α pSpec₁)
    (D₂ : pSpec₁.FullTranscript → SlotDecoder α pSpec₂) :
    (D₁.append D₂).toSlot = do
      let t₁ ← D₁.toSlot
      let t₂ ← (D₂ t₁).toSlot
      return t₁ ++ₜ t₂ := by
  refine Slot.ext fun l ↦ ?_
  simp only [read_toSlot, runFull_append, Slot.read_bind]
  cases D₁.runFull l with
  | none => rfl
  | some p =>
    simp only [Option.bind_some]
    cases (D₂ p.1).runFull p.2 <;> rfl

end ToSlot

end SlotDecoder

end

end LeanerVM.Protocol
