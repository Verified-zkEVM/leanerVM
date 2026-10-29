/-
  LeanerVM.Protocol.ReaderSlots

  The facts a reader of chain histories owes (`SlotReader`), for a decoder built from slots: each
  challenge read off its squeezes, uniform when they are, read by the decoder's slot; slots that
  do not see the state an observe or a nonce step leads to; and the rounds that read a nonce,
  before the marked challenges.
-/

module

public import LeanerVM.Protocol.ChainGroups
public import LeanerVM.Protocol.ToArkLib.DecodeSteps
public import LeanerVM.Protocol.ToArkLib.ScheduleBounds

/-!
# Slots of a reader of chain histories

A decoder of a schedule from the chain's history (`SlotDecoder (Block × Digest) pSpec`) reads each
round by a slot. A `SlotReader` asks four things of it, each proved here once for every decoder
built from slots by `single`, `append`, `draws`, `rounds` and lists of steps, from the same fact
about each slot.

* **Challenges read off squeezes** (`ChalSlots`, `SqueezeReads`). A `UniformSlot C` is a sampler of
  `C` with a squeeze slot on it: the number of squeezes, the challenge their digests give, and that
  uniform digests give a uniform challenge. `ChalSlots pSpec` gives one to every challenge round,
  side by side over appended schedules (`ChalSlots.append`); `SqueezeReads D f` says that the
  decoder's slot at each challenge round reads the squeezes of `f` and gives their challenge,
  whatever the transcript before. Then a history decoded to the start of a challenge, followed by
  its squeezes and anything, decodes past the challenge with the assembled challenge
  (`squeezeSlot_read_of`).
* **Blind to non-squeeze states** (`Slot.Blind`). `view` keeps a squeeze's state and erases every
  other reading's; a blind slot reads a viewed history as it reads the history, viewed. A decoder
  of blind slots decodes a history and its view alike (`decodePrefix_view`), so changing the
  state after an observe or a nonce step changes nothing (`decodePrefix_digest_indep`).
* **Nonce rounds** (`NonceRounds`, `MarkAfter`). `N` flags the rounds whose slot reads exactly one
  nonce step; `MarkAfter pre b N` says every marked challenge follows a flagged round (or, at the
  start, the round before the schedule, when `pre`). A history decoded exactly to the start of a
  marked challenge then ends with a nonce step (`mark_afterNonce_of`).

`SlotDecoder.ReadsWell D f N` bundles the first, the second and the third, built step by step,
also along a list of steps (`SeqSlots`, `SeqFlags`, `SeqDecoder.ReadsWell.toDecoder`); the fourth,
that every challenge reads a squeeze, is `ChalSlots.Pos`. `UniformSlot.slotAt` puts a uniform slot
on any sampler of its type, uniform samplers agreeing.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters Blake2sHash OracleComp OracleSpec ProtocolSpec StepSchedule

@[expose] public section

/-! ## Uniform slots -/

/-- A challenge type read off squeezes: a sampler of it and a squeeze slot on that sampler. -/
structure UniformSlot (C : Type) where
  /-- The sampler. -/
  inst : SampleableType C
  /-- The squeezes and the challenge they give. -/
  slot : @SqueezeSlot C inst

namespace UniformSlot

variable {C : Type}

/-- The number of squeezes. -/
abbrev m (u : UniformSlot C) : ℕ := @SqueezeSlot.m C u.inst u.slot

/-- The challenge the squeezes' digests give. -/
abbrev assemble (u : UniformSlot C) : (Fin u.m → Digest) → C :=
  @SqueezeSlot.assemble C u.inst u.slot

/-- A uniform slot carried along an equality of types, its squeezes unchanged. -/
def cast {C' : Type} (e : C = C') (u : UniformSlot C) : UniformSlot C' where
  inst := e ▸ u.inst
  slot := @SqueezeSlot.mk C' (e ▸ u.inst) u.m (fun ds ↦ _root_.cast e (u.assemble ds))
    (by subst e; exact @SqueezeSlot.uniform C u.inst u.slot)

@[simp] theorem m_cast {C' : Type} (e : C = C') (u : UniformSlot C) : (u.cast e).m = u.m := rfl

private theorem assemble_cast {C' : Type} (e : C = C') (u : UniformSlot C) (ds : Fin u.m → Digest) :
    (u.cast e).assemble ds = _root_.cast e (u.assemble ds) := rfl

/-- The squeeze slot of `u` on any sampler of its type: uniform samplers agree. -/
def slotAt (u : UniformSlot C) (inst : SampleableType C) : @SqueezeSlot C inst :=
  @SqueezeSlot.mk C inst u.m u.assemble fun p ↦
    (@SqueezeSlot.uniform C u.inst u.slot p).trans
      (@SampleableType.prEvent_uniformSample_equiv C C u.inst inst (Equiv.refl C) p)

end UniformSlot

/-! ## Families over a schedule's challenges -/

theorem append_dir_castAdd {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    (i : Fin m) : (pSpec₁ ++ₚ pSpec₂).dir (Fin.castAdd n i) = pSpec₁.dir i := by
  simp only [Fin.vappend_eq_append, Fin.append_left]

theorem append_dir_natAdd {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    (j : Fin n) : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m j) = pSpec₂.dir j := by
  simp only [Fin.vappend_eq_append, Fin.append_right]

/-- A uniform slot for every challenge round of a schedule. -/
abbrev ChalSlots {n : ℕ} (pSpec : ProtocolSpec n) : Type :=
  ∀ k : Fin n, pSpec.dir k = .V_to_P → UniformSlot (pSpec.«Type» k)

namespace ChalSlots

/-- A schedule of no round. -/
def empty {pSpec : ProtocolSpec 0} : ChalSlots pSpec := fun k ↦ k.elim0

/-- A message: no challenge. -/
def say (M : Type) : ChalSlots (say M) := fun ⟨0, _⟩ h ↦ nomatch h

/-- A challenge read by `u`. -/
def draw {C : Type} (u : UniformSlot C) : ChalSlots (draw C) := fun ⟨0, _⟩ _ ↦ u

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Two schedules in sequence: each challenge keeps its slot. -/
def append (f₁ : ChalSlots pSpec₁) (f₂ : ChalSlots pSpec₂) : ChalSlots (pSpec₁ ++ₚ pSpec₂) :=
  Fin.addCases (motive := fun k ↦
      (pSpec₁ ++ₚ pSpec₂).dir k = .V_to_P → UniformSlot ((pSpec₁ ++ₚ pSpec₂).«Type» k))
    (fun i h ↦ (f₁ i (by rwa [append_dir_castAdd] at h)).cast (append_Type_castAdd i).symm)
    (fun j h ↦ (f₂ j (by rwa [append_dir_natAdd] at h)).cast (append_Type_natAdd j).symm)

theorem append_left (f₁ : ChalSlots pSpec₁) (f₂ : ChalSlots pSpec₂) (i : ℕ) (hi : i < m)
    (h : i < m + n) (hd : (pSpec₁ ++ₚ pSpec₂).dir ⟨i, h⟩ = .V_to_P) :
    append f₁ f₂ ⟨i, h⟩ hd = (f₁ ⟨i, hi⟩ (by
        rw [← append_dir_castAdd (pSpec₂ := pSpec₂)]; exact hd)).cast
      (append_Type_castAdd (pSpec₂ := pSpec₂) ⟨i, hi⟩).symm := by
  unfold append
  exact congrFun (Fin.addCases_left (motive := fun k ↦
    (pSpec₁ ++ₚ pSpec₂).dir k = .V_to_P → UniformSlot ((pSpec₁ ++ₚ pSpec₂).«Type» k))
    ⟨i, hi⟩) hd

theorem append_right (f₁ : ChalSlots pSpec₁) (f₂ : ChalSlots pSpec₂) (j : ℕ) (hj : j < n)
    (h : m + j < m + n) (hd : (pSpec₁ ++ₚ pSpec₂).dir ⟨m + j, h⟩ = .V_to_P) :
    append f₁ f₂ ⟨m + j, h⟩ hd = (f₂ ⟨j, hj⟩ (by
        rw [← append_dir_natAdd (pSpec₁ := pSpec₁)]; exact hd)).cast
      (append_Type_natAdd (pSpec₁ := pSpec₁) ⟨j, hj⟩).symm := by
  unfold append
  exact congrFun (Fin.addCases_right (motive := fun k ↦
    (pSpec₁ ++ₚ pSpec₂).dir k = .V_to_P → UniformSlot ((pSpec₁ ++ₚ pSpec₂).«Type» k))
    ⟨j, hj⟩) hd

end ChalSlots

namespace ChalSlots

/-- A message read through an oracle: no challenge. -/
def sayO (M : Type) [OracleInterface M] : ChalSlots (Component.sayO M) := fun ⟨0, _⟩ h ↦ nomatch h

/-- `k` challenges, each read by `u`. -/
def draws {C : Type} (u : UniformSlot C) : (k : ℕ) → ChalSlots (Protocol.draws C k)
  | 0 => empty
  | k + 1 => append (draws u k) (draw u)

/-- `m` sumcheck rounds, each challenge read by `u`. -/
def rounds {C : Type} (u : UniformSlot C) (d : ℕ) : (m : ℕ) → ChalSlots (roundsSpec C d m)
  | 0 => empty
  | m + 1 => append (append (say _) (draw u)) (rounds u d m)

end ChalSlots

/-! ## Challenges read off squeezes -/

section Squeezes

open SlotDecoder

/-- A slot reads the squeezes `u` asks for, whatever follows them, and gives their challenge. -/
def ReadsSqueezes {C : Type} (s : Slot (Block × Digest) C) (u : UniformSlot C) : Prop :=
  ∀ (ds : Fin u.m → Digest) (rest : List (Block × Digest)),
    s.read (squeezeBlocks (List.ofFn ds) ++ rest) = some (u.assemble ds, rest)

/-- A slot of a decoder that reads its squeezes, its value carried along an equality of types. -/
private theorem ReadsSqueezes.map_cast {C C' : Type} (e : C = C') {s : Slot (Block × Digest) C}
    {u : UniformSlot C} (h : ReadsSqueezes s u) :
    ReadsSqueezes (s.map (_root_.cast e)) (u.cast e) :=
  fun ds rest ↦ by
    show (s.read _).map _ = _
    rw [show s.read (squeezeBlocks (List.ofFn ds) ++ rest) = some (u.assemble ds, rest) from
      h ds rest]
    rfl

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- **The decoder's challenge slots read their squeezes**: at every challenge round, whatever the
transcript before, the slot reads the squeezes `f` asks for and gives their challenge. -/
def SqueezeReads (D : SlotDecoder (Block × Digest) pSpec) (f : ChalSlots pSpec) : Prop :=
  ∀ (k : Fin n) (h : pSpec.dir k = .V_to_P) (tr : pSpec.Transcript k.castSucc),
    ReadsSqueezes (D.slot k tr) (f k h)

theorem squeezeReads_empty {pSpec : ProtocolSpec 0} (f : ChalSlots pSpec) :
    SqueezeReads (empty : SlotDecoder (Block × Digest) pSpec) f := fun k ↦ k.elim0

theorem squeezeReads_say {M : Type} (s : Slot (Block × Digest) M) :
    SqueezeReads (single (pSpec := say M) s) (ChalSlots.say M) := fun ⟨0, _⟩ h ↦ nomatch h

private theorem squeezeReads_sayO {M : Type} [OracleInterface M] (s : Slot (Block × Digest) M) :
    SqueezeReads (single (pSpec := Component.sayO M) s) (ChalSlots.sayO M) :=
  fun ⟨0, _⟩ h ↦ nomatch h

theorem squeezeReads_draw {C : Type} {s : Slot (Block × Digest) C} {u : UniformSlot C}
    (hs : ReadsSqueezes s u) : SqueezeReads (single (pSpec := draw C) s) (ChalSlots.draw u) :=
  fun ⟨0, _⟩ _ _ ↦ hs

theorem squeezeReads_append {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {D₁ : SlotDecoder (Block × Digest) pSpec₁}
    {D₂ : pSpec₁.FullTranscript → SlotDecoder (Block × Digest) pSpec₂} {f₁ : ChalSlots pSpec₁}
    {f₂ : ChalSlots pSpec₂} (h₁ : SqueezeReads D₁ f₁) (h₂ : ∀ t, SqueezeReads (D₂ t) f₂) :
    SqueezeReads (D₁.append D₂) (f₁.append f₂) := by
  rintro ⟨k, hk⟩ hd tr
  by_cases hkm : k < m
  · rw [append_slot_left D₁ D₂ k hkm hk tr, ChalSlots.append_left f₁ f₂ k hkm hk hd]
    exact (h₁ _ _ _).map_cast _
  · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
    rw [append_slot_right D₁ D₂ j (by omega) hk tr,
      ChalSlots.append_right f₁ f₂ j (by omega) hk hd]
    exact (h₂ _ _ _ _).map_cast _

theorem squeezeReads_draws {C : Type} {s : Slot (Block × Digest) C} {u : UniformSlot C}
    (hs : ReadsSqueezes s u) : ∀ k, SqueezeReads (SlotDecoder.draws s k) (ChalSlots.draws u k)
  | 0 => squeezeReads_empty _
  | k + 1 => squeezeReads_append (D₁ := SlotDecoder.draws s k) (squeezeReads_draws hs k)
      fun _ ↦ squeezeReads_draw hs

theorem squeezeReads_rounds {C σ : Type} {d : ℕ}
    {poly : σ → Slot (Block × Digest) (Vector C (d + 1))}
    {chal : σ → Slot (Block × Digest) C} {next : σ → (roundSpec C d).FullTranscript → σ}
    {u : UniformSlot C} (hc : ∀ a, ReadsSqueezes (chal a) u) :
    ∀ (a : σ) (m : ℕ), SqueezeReads (rounds poly chal next a m) (ChalSlots.rounds u d m)
  | _, 0 => squeezeReads_empty _
  | a, m + 1 => squeezeReads_append
      (squeezeReads_append (squeezeReads_say _) fun _ ↦ squeezeReads_draw (hc a))
      fun t ↦ squeezeReads_rounds hc (next a t) m

/-- A run of `j + 1` rounds is a run of `j`, then round `j`'s slot. -/
private theorem run_succ_eq_some {D : SlotDecoder (Block × Digest) pSpec} {j : ℕ} {hj : j + 1 ≤ n}
    {l : List (Block × Digest)} {tr : pSpec.Transcript ⟨j + 1, by omega⟩}
    {r : List (Block × Digest)} (h : D.run (j + 1) hj l = some (tr, r)) :
    ∃ t l₁ x, D.run j (by omega) l = some (t, l₁) ∧ (D.slot ⟨j, hj⟩ t).read l₁ = some (x, r) := by
  simp only [run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨t, l₁⟩, ht, ⟨x, r'⟩, hx, he⟩ := h
  obtain ⟨-, rfl⟩ := Prod.mk.inj he
  exact ⟨t, l₁, x, ht, hx⟩

/-- **A challenge reads its squeezes, in the longest-prefix form**: if a history decodes exactly to
the start of a challenge, then the history followed by the challenge's squeezes and anything
decodes past the challenge, with the challenge the squeezes give. -/
theorem squeezeSlot_read_of {D : SlotDecoder (Block × Digest) pSpec} {f : ChalSlots pSpec}
    (hS : SqueezeReads D f) {hs : List (Block × Digest)} (i : pSpec.ChallengeIdx)
    {tr : pSpec.Transcript i.1.castSucc} (h : D.decodePrefix hs = some ⟨i.1.castSucc, tr⟩)
    (hpos : 0 < (f i.1 i.2).m) (ds : Fin (f i.1 i.2).m → Digest) (rest : List (Block × Digest))
    {k : Fin (n + 1)} {tr' : pSpec.Transcript k}
    (h' : D.decodePrefix (hs ++ squeezeBlocks (List.ofFn ds) ++ rest) = some ⟨k, tr'⟩) :
    ∃ hk : i.1.succ.val ≤ k.val,
      FullTranscript.take i.1.succ.val hk tr' = tr.concat ((f i.1 i.2).assemble ds) := by
  have hr : D.run i.1.val (by omega) hs = some (tr, []) :=
    D.decodeAt_eq_some.mp (D.decodePrefix_eq_some_iff.mp h).1
  have hr' : D.run k.val (by omega) (hs ++ (squeezeBlocks (List.ofFn ds) ++ rest)) =
      some (tr', []) := by
    rw [← List.append_assoc]
    exact D.decodeAt_eq_some.mp (D.decodePrefix_eq_some_iff.mp h').1
  have hrun : D.run (i.1.val + 1) i.1.isLt (hs ++ (squeezeBlocks (List.ofFn ds) ++ rest)) =
      some (Transcript.concat (m := i.1) ((f i.1 i.2).assemble ds) tr, rest) := by
    have h₁ := D.run_append hr (squeezeBlocks (List.ofFn ds) ++ rest)
    rw [List.nil_append] at h₁
    simp only [run, h₁, Option.bind_some]
    rw [show (D.slot i.1 tr).read (squeezeBlocks (List.ofFn ds) ++ rest) =
      some ((f i.1 i.2).assemble ds, rest) from hS i.1 i.2 tr ds rest]
    rfl
  have hsq_ne : squeezeBlocks (List.ofFn ds) ≠ [] := by
    rw [squeezeBlocks, ne_eq, List.map_eq_nil_iff, List.ofFn_eq_nil_iff]
    exact Nat.pos_iff_ne_zero.mp hpos
  have hk : i.1.val + 1 ≤ k.val := by
    by_contra hlt
    obtain ⟨r₀, hr₀⟩ := D.run_take hr k.val (by omega)
    have h₂ := D.run_append hr₀ (squeezeBlocks (List.ofFn ds) ++ rest)
    rw [hr'] at h₂
    obtain ⟨-, he⟩ := Prod.mk.inj (Option.some.inj h₂)
    exact hsq_ne (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp he.symm).2).1
  refine ⟨hk, ?_⟩
  obtain ⟨r, hr₂⟩ := D.run_take hr' (i.1.val + 1) hk
  rw [hrun] at hr₂
  exact (Prod.mk.inj (Option.some.inj hr₂)).1.symm

end Squeezes

/-! ## Slots blind to the states of observes and nonces -/

section Blind

open SlotDecoder

/-- A reading with its state erased unless it is a squeeze's. -/
def view : Block × Digest → Block × Digest
  | (.squeeze, d) => (.squeeze, d)
  | (b, _) => (b, default)

/-- Readings that differ only in the state of an observe or a nonce step have one view. -/
private theorem view_eq_of_ne_squeeze {b : Block} (d d' : Digest) (hb : b ≠ .squeeze) :
    view (b, d) = view (b, d') := by
  cases b
  · rfl
  · exact absurd rfl hb
  · rfl

/-- A slot that reads a history's view as it reads the history: the same value, the view of the
same readings left. -/
def Slot.Blind {β : Type} (s : Slot (Block × Digest) β) : Prop :=
  ∀ l, s.read (l.map view) = (s.read l).map fun p ↦ (p.1, p.2.map view)

namespace Slot.Blind

variable {β γ : Type}

theorem pure (x : β) : Slot.Blind (Pure.pure x : Slot (Block × Digest) β) := fun _ ↦ rfl

theorem fail : Slot.Blind (Slot.fail : Slot (Block × Digest) β) := fun _ ↦ rfl

theorem next {f : Block × Digest → Option β} (hf : ∀ a, f (view a) = f a) :
    Slot.Blind (Slot.next f) := by
  rintro (_ | ⟨a, l⟩)
  · rfl
  · simp only [List.map_cons, Slot.read_next_cons, hf, Option.map_map]
    rfl

theorem bind {s : Slot (Block × Digest) β} {f : β → Slot (Block × Digest) γ} (hs : s.Blind)
    (hf : ∀ x, (f x).Blind) : Slot.Blind (s >>= f) := by
  intro l
  rw [Slot.read_bind, Slot.read_bind, hs l]
  rcases s.read l with _ | ⟨x, r⟩
  · rfl
  · exact hf x r

theorem map {s : Slot (Block × Digest) β} (hs : s.Blind) (g : β → γ) : (s.map g).Blind := by
  intro l
  show (s.read _).map _ = ((s.read l).map _).map _
  rw [hs l]
  rcases s.read l with _ | ⟨x, r⟩ <;> rfl

theorem mapM {s : Slot (Block × Digest) β} (hs : s.Blind) (g : β → γ) : (g <$> s).Blind := by
  intro l
  rw [Slot.read_mapM, Slot.read_mapM, hs l]
  rcases s.read l with _ | ⟨x, r⟩ <;> rfl

end Slot.Blind

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- A decoder of blind slots. -/
def SlotDecoder.Blind (D : SlotDecoder (Block × Digest) pSpec) : Prop :=
  ∀ k tr, (D.slot k tr).Blind

theorem blind_empty {pSpec : ProtocolSpec 0} :
    (empty : SlotDecoder (Block × Digest) pSpec).Blind := fun k ↦ k.elim0

theorem blind_single {pSpec : ProtocolSpec 1} {s : Slot (Block × Digest) (pSpec.«Type» 0)}
    (hs : s.Blind) : (single s).Blind := fun ⟨0, _⟩ _ ↦ hs

theorem blind_append {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {D₁ : SlotDecoder (Block × Digest) pSpec₁}
    {D₂ : pSpec₁.FullTranscript → SlotDecoder (Block × Digest) pSpec₂} (h₁ : D₁.Blind)
    (h₂ : ∀ t, (D₂ t).Blind) : (D₁.append D₂).Blind := by
  rintro ⟨k, hk⟩ tr
  by_cases hkm : k < m
  · rw [append_slot_left D₁ D₂ k hkm hk tr]
    exact (h₁ _ _).map _
  · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
    rw [append_slot_right D₁ D₂ j (by omega) hk tr]
    exact (h₂ _ _ _).map _

theorem blind_draws {C : Type} {s : Slot (Block × Digest) C} (hs : s.Blind) :
    ∀ k, (SlotDecoder.draws s k).Blind
  | 0 => blind_empty
  | k + 1 => blind_append (blind_draws hs k) fun _ ↦ blind_single hs

theorem blind_rounds {C σ : Type} {d : ℕ} {poly : σ → Slot (Block × Digest) (Vector C (d + 1))}
    {chal : σ → Slot (Block × Digest) C} {next : σ → (roundSpec C d).FullTranscript → σ}
    (hp : ∀ a, (poly a).Blind) (hc : ∀ a, (chal a).Blind) :
    ∀ (a : σ) (m : ℕ), (rounds poly chal next a m).Blind
  | _, 0 => blind_empty
  | a, m + 1 => blind_append (blind_append (blind_single (hp a)) fun _ ↦ blind_single (hc a))
      fun t ↦ blind_rounds hp hc (next a t) m

/-- A decoder of blind slots runs on a history's view as on the history. -/
theorem SlotDecoder.Blind.run {D : SlotDecoder (Block × Digest) pSpec} (hD : D.Blind) :
    ∀ (i : ℕ) (hi : i ≤ n) (l : List (Block × Digest)),
      D.run i hi (l.map view) = (D.run i hi l).map fun p ↦ (p.1, p.2.map view)
  | 0, _, _ => rfl
  | i + 1, hi, l => by
    simp only [SlotDecoder.run, hD.run i (by omega) l]
    rcases D.run i (by omega) l with _ | ⟨t, r⟩
    · rfl
    · simp only [Option.map_some, Option.bind_some, hD ⟨i, hi⟩ t r, Option.map_map]
      rfl

theorem SlotDecoder.Blind.decodeAt {D : SlotDecoder (Block × Digest) pSpec} (hD : D.Blind)
    (i : Fin (n + 1)) (l : List (Block × Digest)) :
    D.decodeAt i (l.map view) = D.decodeAt i l := by
  apply Option.ext
  intro tr
  rw [D.decodeAt_eq_some, D.decodeAt_eq_some, hD.run]
  constructor
  · intro h
    obtain ⟨⟨t, r⟩, ht, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq, List.map_eq_nil_iff] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ht
  · intro h
    rw [h]
    rfl

/-- **A decoder of blind slots decodes a history's view as the history.** -/
theorem SlotDecoder.Blind.decodePrefix_view {D : SlotDecoder (Block × Digest) pSpec}
    (hD : D.Blind) (l : List (Block × Digest)) :
    D.decodePrefix (l.map view) = D.decodePrefix l := by
  rcases h : D.decodePrefix l with _ | ⟨i, tr⟩
  · rw [D.decodePrefix_eq_none_iff] at h ⊢
    intro i
    rw [hD.decodeAt]
    exact h i
  · rw [D.decodePrefix_eq_some_iff] at h ⊢
    refine ⟨by rw [hD.decodeAt]; exact h.1, fun j hj ↦ ?_⟩
    rw [hD.decodeAt]
    exact h.2 j hj

/-- **No slot reads the state an observe or a nonce step leads to.** -/
theorem SlotDecoder.Blind.decodePrefix_digest_indep {D : SlotDecoder (Block × Digest) pSpec}
    (hD : D.Blind) (hs : List (Block × Digest)) {b : Block} (d d' : Digest)
    (rest : List (Block × Digest)) (hb : b ≠ .squeeze) :
    D.decodePrefix (hs ++ (b, d) :: rest) = D.decodePrefix (hs ++ (b, d') :: rest) := by
  rw [← hD.decodePrefix_view, ← hD.decodePrefix_view (hs ++ (b, d') :: rest)]
  simp [view_eq_of_ne_squeeze d d' hb]

end Blind

/-! ## Nonce rounds and the challenges after them -/

section Nonce

open SlotDecoder

/-- A slot that reads exactly one nonce step. -/
def Slot.ReadsNonce {β : Type} (s : Slot (Block × Digest) β) : Prop :=
  ∀ l x r, s.read l = some (x, r) → ∃ n d, l = (.nonce n, d) :: r

theorem Slot.ReadsNonce.map {β γ : Type} {s : Slot (Block × Digest) β} (hs : s.ReadsNonce)
    (g : β → γ) : (s.map g).ReadsNonce := fun l x r h ↦ by
  obtain ⟨⟨y, r'⟩, hy, he⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨-, rfl⟩ := Prod.mk.inj he
  exact hs l y r' hy

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- The rounds flagged by `N` read exactly one nonce step. -/
def SlotDecoder.NonceRounds (D : SlotDecoder (Block × Digest) pSpec) (N : Fin n → Bool) : Prop :=
  ∀ k tr, N k = true → (D.slot k tr).ReadsNonce

private theorem nonceRounds_none (D : SlotDecoder (Block × Digest) pSpec) :
    D.NonceRounds fun _ ↦ false := fun _ _ h ↦ nomatch h

private theorem nonceRounds_single {pSpec : ProtocolSpec 1}
    {s : Slot (Block × Digest) (pSpec.«Type» 0)} (hs : s.ReadsNonce) :
    (single s).NonceRounds fun _ ↦ true := fun ⟨0, _⟩ _ _ ↦ hs

private theorem nonceRounds_append {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {D₁ : SlotDecoder (Block × Digest) pSpec₁}
    {D₂ : pSpec₁.FullTranscript → SlotDecoder (Block × Digest) pSpec₂} {N₁ : Fin m → Bool}
    {N₂ : Fin n → Bool} (h₁ : D₁.NonceRounds N₁) (h₂ : ∀ t, (D₂ t).NonceRounds N₂) :
    (D₁.append D₂).NonceRounds (Fin.append N₁ N₂) := by
  rintro ⟨k, hk⟩ tr hN
  by_cases hkm : k < m
  · rw [append_slot_left D₁ D₂ k hkm hk tr]
    refine (h₁ _ _ ?_).map _
    rwa [show (⟨k, hk⟩ : Fin (m + n)) = Fin.castAdd n ⟨k, hkm⟩ from rfl, Fin.append_left] at hN
  · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
    rw [append_slot_right D₁ D₂ j (by omega) hk tr]
    refine (h₂ _ _ _ ?_).map _
    rwa [show (⟨m + j, hk⟩ : Fin (m + n)) = Fin.natAdd m ⟨j, by omega⟩ from rfl,
      Fin.append_right] at hN

/-- The flag of the round before a schedule's: its last round's, or `pre` for no round. -/
def lastFlag {m : ℕ} (pre : Bool) (N : Fin m → Bool) : Bool :=
  if h : 0 < m then N ⟨m - 1, by omega⟩ else pre

/-- **Every marked challenge follows a flagged round**: the round before it, or, for the first
round, the round before the schedule when `pre`. -/
def MarkAfter (pre : Bool) (b : pSpec.ChallengeIdx → Bool) (N : Fin n → Bool) : Prop :=
  ∀ i, b i = true → (i.1.val = 0 ∧ pre = true) ∨ ∃ j : Fin n, j.val + 1 = i.1.val ∧ N j = true

theorem markAfter_none (pre : Bool) (N : Fin n → Bool) :
    MarkAfter (pSpec := pSpec) pre (fun _ ↦ false) N := fun _ h ↦ nomatch h

theorem markAfter_append {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {pre : Bool} {b₁ : pSpec₁.ChallengeIdx → Bool} {b₂ : pSpec₂.ChallengeIdx → Bool}
    {N₁ : Fin m → Bool} {N₂ : Fin n → Bool} (h₁ : MarkAfter pre b₁ N₁)
    (h₂ : MarkAfter (lastFlag pre N₁) b₂ N₂) :
    MarkAfter pre (markAppend b₁ b₂) (Fin.append N₁ N₂) := by
  intro i hb
  obtain ⟨x, rfl⟩ := ChallengeIdx.sumEquiv.surjective i
  rw [markAppend, Function.comp_apply, Equiv.symm_apply_apply] at hb
  rcases x with j | j
  · rcases h₁ j hb with ⟨h0, hp⟩ | ⟨j', hj', hN⟩
    · exact .inl ⟨h0, hp⟩
    · refine .inr ⟨Fin.castAdd n j', hj', ?_⟩
      rw [Fin.append_left]
      exact hN
  · rcases h₂ j hb with ⟨h0, hp⟩ | ⟨j', hj', hN⟩
    · unfold lastFlag at hp
      split at hp
      · rename_i hm
        refine .inr ⟨Fin.castAdd n ⟨m - 1, by omega⟩, ?_, ?_⟩
        · show m - 1 + 1 = m + j.1.val
          omega
        · rw [Fin.append_left]
          exact hp
      · refine .inl ⟨?_, hp⟩
        show m + j.1.val = 0
        omega
    · refine .inr ⟨Fin.natAdd m j', ?_, ?_⟩
      · show m + j'.val + 1 = m + j.1.val
        omega
      · rw [Fin.append_right]
        exact hN

/-- **A marked challenge follows a nonce step**: a history decoded exactly to the start of a marked
challenge ends with a nonce step. -/
theorem mark_afterNonce_of {D : SlotDecoder (Block × Digest) pSpec} {N : Fin n → Bool}
    {b : pSpec.ChallengeIdx → Bool} (hN : D.NonceRounds N) (hM : MarkAfter false b N)
    {hs : List (Block × Digest)} (i : pSpec.ChallengeIdx) {tr : pSpec.Transcript i.1.castSucc}
    (h : D.decodePrefix hs = some ⟨i.1.castSucc, tr⟩) (hb : b i = true) :
    ∃ hs₀ n d, hs = hs₀ ++ [(.nonce n, d)] := by
  rcases hM i hb with ⟨-, hp⟩ | ⟨j, hj, hNj⟩
  · exact nomatch hp
  have hr : D.run i.1.val (by omega) hs = some (tr, []) :=
    D.decodeAt_eq_some.mp (D.decodePrefix_eq_some_iff.mp h).1
  obtain ⟨⟨k, hk⟩, hd⟩ := i
  simp only at hj hr
  subst hj
  obtain ⟨t, l₁, x, ht, hx⟩ := run_succ_eq_some hr
  obtain ⟨n', d, rfl⟩ := hN j t hNj l₁ x [] hx
  obtain ⟨c, rfl, -⟩ := D.run_eq_some_iff.mp ht
  exact ⟨c, n', d, rfl⟩

end Nonce

/-! ## Every challenge reads a squeeze -/

namespace ChalSlots

/-- Every challenge round reads a squeeze at least. -/
def Pos {n : ℕ} {pSpec : ProtocolSpec n} (f : ChalSlots pSpec) : Prop := ∀ k h, 0 < (f k h).m

theorem pos_empty {pSpec : ProtocolSpec 0} : (empty : ChalSlots pSpec).Pos := fun k ↦ k.elim0

theorem pos_say (M : Type) : (say M).Pos := fun ⟨0, _⟩ h ↦ nomatch h

theorem pos_sayO (M : Type) [OracleInterface M] : (sayO M).Pos := fun ⟨0, _⟩ h ↦ nomatch h

theorem pos_draw {C : Type} {u : UniformSlot C} (hu : 0 < u.m) : (draw u).Pos :=
  fun ⟨0, _⟩ _ ↦ hu

theorem pos_append {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {f₁ : ChalSlots pSpec₁} {f₂ : ChalSlots pSpec₂} (h₁ : f₁.Pos) (h₂ : f₂.Pos) :
    (append f₁ f₂).Pos := by
  rintro ⟨k, hk⟩ hd
  by_cases hkm : k < m
  · rw [append_left f₁ f₂ k hkm hk hd, UniformSlot.m_cast]
    exact h₁ _ _
  · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
    rw [append_right f₁ f₂ j (by omega) hk hd, UniformSlot.m_cast]
    exact h₂ _ _

theorem pos_draws {C : Type} {u : UniformSlot C} (hu : 0 < u.m) : ∀ k, (draws u k).Pos
  | 0 => pos_empty
  | k + 1 => pos_append (pos_draws hu k) (pos_draw hu)

theorem pos_rounds {C : Type} {u : UniformSlot C} (hu : 0 < u.m) (d : ℕ) :
    ∀ m, (rounds u d m).Pos
  | 0 => pos_empty
  | m + 1 => pos_append (pos_append (pos_say _) (pos_draw hu)) (pos_rounds hu d m)

end ChalSlots

/-! ## Decoders that read well -/

section Well

open SlotDecoder

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- **A decoder that reads well** by the slots `f` and the nonce flags `N`: its challenges read
their squeezes, its slots are blind, and its flagged rounds read a nonce. -/
structure SlotDecoder.ReadsWell (D : SlotDecoder (Block × Digest) pSpec) (f : ChalSlots pSpec)
    (N : Fin n → Bool) : Prop where
  /-- The challenges read their squeezes. -/
  squeezes : SqueezeReads D f
  /-- The slots are blind. -/
  blind : D.Blind
  /-- The flagged rounds read a nonce. -/
  nonce : D.NonceRounds N

theorem readsWell_empty {pSpec : ProtocolSpec 0} :
    (empty : SlotDecoder (Block × Digest) pSpec).ReadsWell ChalSlots.empty fun _ ↦ false :=
  ⟨squeezeReads_empty _, blind_empty, nonceRounds_none _⟩

theorem readsWell_say {M : Type} {s : Slot (Block × Digest) M} (hs : s.Blind) :
    (single (pSpec := say M) s).ReadsWell (ChalSlots.say M) fun _ ↦ false :=
  ⟨squeezeReads_say s, blind_single hs, nonceRounds_none _⟩

theorem readsWell_nonce {M : Type} {s : Slot (Block × Digest) M} (hs : s.Blind)
    (hn : s.ReadsNonce) : (single (pSpec := say M) s).ReadsWell (ChalSlots.say M) fun _ ↦ true :=
  ⟨squeezeReads_say s, blind_single hs, nonceRounds_single hn⟩

theorem readsWell_sayO {M : Type} [OracleInterface M] {s : Slot (Block × Digest) M}
    (hs : s.Blind) :
    (single (pSpec := Component.sayO M) s).ReadsWell (ChalSlots.sayO M) fun _ ↦ false :=
  ⟨squeezeReads_sayO s, blind_single hs, nonceRounds_none _⟩

theorem readsWell_draw {C : Type} {s : Slot (Block × Digest) C} {u : UniformSlot C}
    (hr : ReadsSqueezes s u) (hs : s.Blind) :
    (single (pSpec := draw C) s).ReadsWell (ChalSlots.draw u) fun _ ↦ false :=
  ⟨squeezeReads_draw hr, blind_single hs, nonceRounds_none _⟩

theorem readsWell_append {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {D₁ : SlotDecoder (Block × Digest) pSpec₁}
    {D₂ : pSpec₁.FullTranscript → SlotDecoder (Block × Digest) pSpec₂} {f₁ : ChalSlots pSpec₁}
    {f₂ : ChalSlots pSpec₂} {N₁ : Fin m → Bool} {N₂ : Fin n → Bool} (h₁ : D₁.ReadsWell f₁ N₁)
    (h₂ : ∀ t, (D₂ t).ReadsWell f₂ N₂) :
    (D₁.append D₂).ReadsWell (f₁.append f₂) (Fin.append N₁ N₂) :=
  ⟨squeezeReads_append h₁.squeezes fun t ↦ (h₂ t).squeezes,
    blind_append h₁.blind fun t ↦ (h₂ t).blind,
    nonceRounds_append h₁.nonce fun t ↦ (h₂ t).nonce⟩

/-- A decoder whose slots read squeezes and are blind reads well with no nonce. -/
theorem SlotDecoder.ReadsWell.of_squeezes {D : SlotDecoder (Block × Digest) pSpec}
    {f : ChalSlots pSpec} (hS : SqueezeReads D f) (hB : D.Blind) : D.ReadsWell f fun _ ↦ false :=
  ⟨hS, hB, nonceRounds_none D⟩

/-- Appended decoders that read well with no nonce read well with no nonce. -/
theorem readsWell_append_none {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {D₁ : SlotDecoder (Block × Digest) pSpec₁}
    {D₂ : pSpec₁.FullTranscript → SlotDecoder (Block × Digest) pSpec₂} {f₁ : ChalSlots pSpec₁}
    {f₂ : ChalSlots pSpec₂} (h₁ : D₁.ReadsWell f₁ fun _ ↦ false)
    (h₂ : ∀ t, (D₂ t).ReadsWell f₂ fun _ ↦ false) :
    (D₁.append D₂).ReadsWell (f₁.append f₂) fun _ ↦ false :=
  .of_squeezes (squeezeReads_append h₁.squeezes fun t ↦ (h₂ t).squeezes)
    (blind_append h₁.blind fun t ↦ (h₂ t).blind)

end Well

/-! ## Along a list of steps -/

section Seq

/-- Challenge slots along a list of steps, a family for each step. -/
def SeqSlots : List Step → Type
  | [] => PUnit
  | a :: l => ChalSlots a.spec × SeqSlots l

/-- The family of the steps' schedule: the steps' families in sequence. -/
def SeqSlots.toFam : {l : List Step} → SeqSlots l → ChalSlots (seqSpec l)
  | [], _ => ChalSlots.empty
  | _ :: _, F => ChalSlots.append F.1 F.2.toFam

/-- Nonce flags along a list of steps, flags for each step. -/
def SeqFlags : List Step → Type
  | [] => PUnit
  | a :: l => (Fin a.n → Bool) × SeqFlags l

/-- The flags of the steps' schedule: the steps' flags in sequence. -/
def SeqFlags.toFlags : {l : List Step} → SeqFlags l → Fin (seqRounds l) → Bool
  | [], _ => fun _ ↦ false
  | _ :: _, N => Fin.append N.1 N.2.toFlags

/-- **Every step reads well**, whatever the transcripts before it. -/
def SeqDecoder.ReadsWell : {l : List Step} → SeqDecoder (Block × Digest) l → SeqSlots l →
    SeqFlags l → Prop
  | [], _, _, _ => True
  | _ :: _, D, F, N => D.1.ReadsWell F.1 N.1 ∧ ∀ t, SeqDecoder.ReadsWell (D.2 t) F.2 N.2

/-- A list of steps that read well is a decoder that reads well. -/
theorem SeqDecoder.ReadsWell.toDecoder : ∀ {l : List Step} {D : SeqDecoder (Block × Digest) l}
    {F : SeqSlots l} {N : SeqFlags l}, D.ReadsWell F N → D.toDecoder.ReadsWell F.toFam N.toFlags
  | [], _, _, _, _ => readsWell_empty
  | _ :: _, _, _, _, h => readsWell_append h.1 fun t ↦ (h.2 t).toDecoder

/-- Every step's challenges read a squeeze at least. -/
def SeqSlots.Pos : {l : List Step} → SeqSlots l → Prop
  | [], _ => True
  | _ :: _, F => F.1.Pos ∧ SeqSlots.Pos F.2

theorem SeqSlots.Pos.toFam : ∀ {l : List Step} {F : SeqSlots l}, F.Pos → F.toFam.Pos
  | [], _, _ => ChalSlots.pos_empty
  | _ :: _, _, h => ChalSlots.pos_append h.1 h.2.toFam

end Seq

/-! ## Marks after a nonce -/

theorem markAfter_draw {C : Type} {pre : Bool} (hp : pre = true) (N : Fin 1 → Bool) :
    MarkAfter (pSpec := draw C) pre (fun _ ↦ true) N :=
  fun i _ ↦ .inl ⟨Nat.lt_one_iff.mp i.1.isLt, hp⟩

end

end LeanerVM.Protocol
