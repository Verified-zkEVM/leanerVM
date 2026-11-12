/-
  LeanerVM.Protocol.DecodeAgree

  Where the decoder of leanVM's chain history reads: every phase reads a fixed number of readings,
  so each word enters the decoded transcript only after the readings of its root, at the reading
  offsets the reader takes the roots at; decoders whose words agree on every root a history carries
  decode the history alike.
-/

module

public import LeanerVM.Protocol.ProofRoots

/-!
# The decoder reads every word after its root

The compiled decoder at the words `W` (`DecodeChain.compiledDec`) reads a word in two places: the
oracle message of a commitment, the round that reads the commitment's root, and the claims rebuilt
after the level's query positions, past that root. `ReadsN D N`: every full run of `D` reads
exactly `N` readings, true of every phase of the decoder (`readsN_busDec`, `readsN_tableDec`,
`readsN_pubDec`, `readsN_flockDec`, `readsN_frontDec`), with the counts of the walk counted in
readings (`readingCounts`): so the decoder reads level `j`'s root at the reading offset the walk
reads it at (`ProofRoots.rootOffsets readingCounts`).

`AgreeAt D D' p N`: at every state `D` reaches from reading `p` of a history of `N` readings, the
two decoders' slots read alike (`AgreeAt.run`: they run alike). Words that agree on every word whose
root lies within the history (`WordsAgree N W W'`) give decoders that agree from reading `0`
(`agreeAt_compiledDec`), hence `decodePrefix_words_congr`: a history decodes to the same transcript
prefix with either. With one family of words, a history's prefix decodes to the first rounds of the
history's decoded transcript (`decodePrefix_take`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa ProtocolSpec StepSchedule Verify
open Whir DecodeChain ProofRoots SlotDecoder

@[expose] public section

namespace DecodeAgree

/-! ## Decoders that read a fixed number of readings -/

section Generic

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- A decoder every full run of which reads exactly `N` readings. -/
def ReadsN (D : SlotDecoder Reading pSpec) (N : ℕ) : Prop := readGrade.P D.toSlot N

theorem ReadsN.of_eq {D : SlotDecoder Reading pSpec} {N N' : ℕ} (h : ReadsN D N) (e : N = N') :
    ReadsN D N' := e ▸ h

theorem readsN_empty {pSpec : ProtocolSpec 0} : ReadsN (empty : SlotDecoder Reading pSpec) 0 :=
  readGrade.pure _

theorem readsN_single {pSpec : ProtocolSpec 1} {s : Slot Reading (pSpec.«Type» 0)} {k : ℕ}
    (hs : readGrade.P s k) : ReadsN (single s) k := by
  rw [ReadsN, toSlot_single]
  exact readGrade.map hs _

theorem readsN_append {m n₂ : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n₂}
    {D₁ : SlotDecoder Reading pSpec₁} {D₂ : pSpec₁.FullTranscript → SlotDecoder Reading pSpec₂}
    {N₁ N₂ : ℕ} (h₁ : ReadsN D₁ N₁) (h₂ : ∀ t, ReadsN (D₂ t) N₂) :
    ReadsN (D₁.append D₂) (N₁ + N₂) := by
  rw [ReadsN, toSlot_append]
  exact readGrade.of_eq (readGrade.bind h₁ fun t ↦ readGrade.bind (h₂ t) fun _ ↦ readGrade.pure _)
    rfl

theorem readsN_draws {C : Type} {s : Slot Reading C} (hs : readGrade.P s 1) :
    ∀ k, ReadsN (SlotDecoder.draws s k) k
  | 0 => readsN_empty
  | k + 1 => readsN_append (readsN_draws hs k) fun _ ↦ readsN_single hs

theorem readsN_rounds {C σ : Type} {d : ℕ} {poly : σ → Slot Reading (Vector C (d + 1))}
    {chal : σ → Slot Reading C} {next : σ → (roundSpec C d).FullTranscript → σ}
    (hp : ∀ a, readGrade.P (poly a) d) (hc : ∀ a, readGrade.P (chal a) 1) :
    ∀ (a : σ) (m : ℕ), ReadsN (SlotDecoder.rounds poly chal next a m) (m * (d + 1))
  | _, 0 => readsN_empty.of_eq (by simp)
  | a, m + 1 =>
    (readsN_append (readsN_append (readsN_single (hp a)) fun _ ↦ readsN_single (hc a))
      fun t ↦ readsN_rounds hp hc (next a t) m).of_eq (by ring)

/-- The runs of a decoder whose round `k` reads `g k` readings read the counts of their rounds. -/
private theorem run_length_of_slots {D : SlotDecoder Reading pSpec} {g : Fin n → ℕ}
    (hg : ∀ k tr, readGrade.P (D.slot k tr) (g k)) :
    ∀ i (hi : i ≤ n) l tr r, D.run i hi l = some (tr, r) →
      ∃ c, l = c ++ r ∧ c.length = ∑ k : Fin i, g (Fin.castLE hi k)
  | 0, _, l, tr, r, h => by
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨[], rfl, by simp⟩
  | i + 1, hi, l, tr, r, h => by
    simp only [SlotDecoder.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨t, s⟩, hp, ⟨x, s'⟩, hq, he⟩ := h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    obtain ⟨c₁, rfl, hc₁⟩ := run_length_of_slots hg i (by omega) l t s hp
    obtain ⟨c₂, rfl, hc₂⟩ := hg ⟨i, hi⟩ t _ _ _ hq
    exact ⟨c₁ ++ c₂, by simp, by rw [List.length_append, hc₁, hc₂, Fin.sum_univ_castSucc]; rfl⟩

/-- A graded slot reads nothing off fewer readings than its count. -/
private theorem read_eq_none_of_lt {β : Type} {s : Slot Reading β} {k : ℕ} (hs : readGrade.P s k)
    {r : List Reading} (h : r.length < k) : s.read r = none := by
  rcases hr : s.read r with _ | ⟨x, r'⟩
  · rfl
  · obtain ⟨c, rfl, hc⟩ := hs _ _ _ hr
    simp only [List.length_append] at h
    omega

/-! ## Decoders that read alike from a position -/

/-- **Two decoders that agree from position `p`** of a history of `N` readings: at every state the
first reaches from reading `p`, their slots read alike. -/
def AgreeAt (D D' : SlotDecoder Reading pSpec) (p N : ℕ) : Prop :=
  ∀ (k : ℕ) (hk : k < n) (l : List Reading) tr r, p + l.length = N →
    D.run k hk.le l = some (tr, r) → (D.slot ⟨k, hk⟩ tr).read r = (D'.slot ⟨k, hk⟩ tr).read r

private theorem agreeAt_refl (D : SlotDecoder Reading pSpec) (p N : ℕ) : AgreeAt D D p N :=
  fun _ _ _ _ _ _ _ ↦ rfl

/-- Past the end of the history, any decoders agree. -/
private theorem agreeAt_of_lt {D D' : SlotDecoder Reading pSpec} {p N : ℕ} (h : N < p) :
    AgreeAt D D' p N :=
  fun _ _ _ _ _ hl _ ↦ absurd hl (by omega)

theorem AgreeAt.of_eq {D D' : SlotDecoder Reading pSpec} {p p' N : ℕ} (h : AgreeAt D D' p N)
    (e : p = p') : AgreeAt D D' p' N := e ▸ h

/-- **Decoders that agree from position `p` run alike** on the last readings of the history. -/
theorem AgreeAt.run {D D' : SlotDecoder Reading pSpec} {p N : ℕ} (h : AgreeAt D D' p N)
    {l : List Reading} (hl : p + l.length = N) : ∀ k (hk : k ≤ n), D.run k hk l = D'.run k hk l
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := AgreeAt.run h hl k (by omega)
    simp only [SlotDecoder.run]
    rw [← ih]
    rcases hr : D.run k (by omega) l with _ | ⟨tr, r⟩
    · rfl
    · simp only [Option.bind_some]
      rw [h k hk l tr r hl hr]

/-- Decoders that run alike decode the same rounds. -/
private theorem decodeAt_congr {D D' : SlotDecoder Reading pSpec} {l : List Reading}
    (h : ∀ k (hk : k ≤ n), D.run k hk l = D'.run k hk l) (i : Fin (n + 1)) :
    D.decodeAt i l = D'.decodeAt i l :=
  Option.ext fun tr ↦ by
    simp only [D.decodeAt_eq_some, D'.decodeAt_eq_some, h]

/-- **Decoders that run alike decode the same prefix.** -/
theorem decodePrefix_congr {D D' : SlotDecoder Reading pSpec} {l : List Reading}
    (h : ∀ k (hk : k ≤ n), D.run k hk l = D'.run k hk l) :
    D.decodePrefix l = D'.decodePrefix l := by
  have hd := decodeAt_congr h
  rcases hD : D.decodePrefix l with _ | ⟨i, tr⟩
  · refine (D'.decodePrefix_eq_none_iff.mpr fun i ↦ ?_).symm
    rw [← hd]
    exact D.decodePrefix_eq_none_iff.mp hD i
  · refine (D'.decodePrefix_eq_some_iff.mpr ⟨?_, fun j hj ↦ ?_⟩).symm
    · rw [← hd]
      exact (D.decodePrefix_eq_some_iff.mp hD).1
    · rw [← hd]
      exact (D.decodePrefix_eq_some_iff.mp hD).2 j hj

private theorem agreeAt_single {pSpec : ProtocolSpec 1} {s s' : Slot Reading (pSpec.«Type» 0)}
    {p N : ℕ}
    (h : ∀ r : List Reading, p + r.length = N → s.read r = s'.read r) :
    AgreeAt (single s) (single s') p N := by
  intro k hk l tr r hl hr
  obtain rfl : k = 0 := by omega
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
  exact h l hl

variable {m n₂ : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n₂}

/-- **Appended decoders agree** when the first parts agree and, from where the first part ends,
the second parts do. -/
theorem agreeAt_append {D₁ D₁' : SlotDecoder Reading pSpec₁}
    {D₂ D₂' : pSpec₁.FullTranscript → SlotDecoder Reading pSpec₂} {p N N₁ : ℕ}
    (h₁ : AgreeAt D₁ D₁' p N) (hN : ReadsN D₁ N₁) (h₂ : ∀ t, AgreeAt (D₂ t) (D₂' t) (p + N₁) N) :
    AgreeAt (D₁.append D₂) (D₁'.append D₂') p N := by
  intro k hk l tr r hl hr
  by_cases hkm : k < m
  · rw [append_slot_left D₁ D₂ k hkm hk tr, append_slot_left D₁' D₂' k hkm hk tr]
    have h₀ := run_append_left D₁ D₂ k (by omega) l
    rw [hr, Option.map_some] at h₀
    change ((D₁.slot _ _).read r).map _ = ((D₁'.slot _ _).read r).map _
    rw [h₁ k hkm l _ r hl h₀.symm]
  · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
    rw [append_slot_right D₁ D₂ j (by omega) hk tr, append_slot_right D₁' D₂' j (by omega) hk tr]
    have h₀ := run_append_right D₁ D₂ j (by omega) l
    rw [hr, Option.map_some, eq_comm, Option.bind_eq_some_iff] at h₀
    obtain ⟨⟨t₁, r₁⟩, hf, hq⟩ := h₀
    obtain ⟨⟨t₂, r₂⟩, hq', he⟩ := Option.map_eq_some_iff.mp hq
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨c₁, rfl, hc₁⟩ := hN _ _ _ hf
    change (((D₂ _).slot _ _).read r₂).map _ = (((D₂' _).slot _ _).read r₂).map _
    rw [h₂ _ j (by omega) r₁ _ r₂ (by simp only [List.length_append] at hl; omega) hq']

/-- Appended decoders with one second part agree when the first parts do. -/
private theorem agreeAt_append_same {D₁ D₁' : SlotDecoder Reading pSpec₁}
    {D₂ : pSpec₁.FullTranscript → SlotDecoder Reading pSpec₂} {p N : ℕ} (h₁ : AgreeAt D₁ D₁' p N) :
    AgreeAt (D₁.append D₂) (D₁'.append D₂) p N := by
  intro k hk l tr r hl hr
  by_cases hkm : k < m
  · rw [append_slot_left D₁ D₂ k hkm hk tr, append_slot_left D₁' D₂ k hkm hk tr]
    have h₀ := run_append_left D₁ D₂ k (by omega) l
    rw [hr, Option.map_some] at h₀
    change ((D₁.slot _ _).read r).map _ = ((D₁'.slot _ _).read r).map _
    rw [h₁ k hkm l _ r hl h₀.symm]
  · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
    rw [append_slot_right D₁ D₂ j (by omega) hk tr, append_slot_right D₁' D₂ j (by omega) hk tr]

end Generic

/-! ## The readings of leanVM's slots -/

private theorem rg_sample : readGrade.P historyOps.sample 1 := historyOps_readGraded.sample

private theorem rg_nextScalar : readGrade.P historyOps.nextScalar 1 :=
  historyOps_readGraded.nextScalar

private theorem rg_nextRoot : readGrade.P historyOps.nextRoot 2 := historyOps_readGraded.nextRoot

private theorem rg_checkPow (bits : ℕ) : readGrade.P (historyOps.checkPow bits) 1 :=
  historyOps_readGraded.checkPow bits

private theorem rg_fail {β : Type} (k : ℕ) : readGrade.P (Slot.fail : Slot Reading β) k :=
  fun _ _ _ h ↦ nomatch h

private theorem rg_nextScalars (k : ℕ) : readGrade.P (historyOps.nextScalars k) k :=
  readGrade.of_eq (nextScalars_grade historyOps_readGraded k) (by simp [readingCounts])

private theorem rg_samples (k : ℕ) : readGrade.P (samples historyOps k) k :=
  readGrade.of_eq (samples_grade historyOps_readGraded k) (by simp [readingCounts])

private theorem rg_vecSlot (k : ℕ) : readGrade.P (vecSlot k) k := readGrade.map (rg_nextScalars k) _

private theorem rg_polySlot (d : ℕ) (claim : Thunk E) (eq? : Thunk (Option E)) :
    readGrade.P (polySlot d claim eq?) d := by
  refine readGrade.of_eq (readGrade.bind (k := 0) (rg_nextScalars d) fun w ↦ ?_) (Nat.add_zero d)
  split
  · exact readGrade.pure _
  · exact rg_fail _

private theorem rg_positionsSlot (b t : ℕ) :
    readGrade.P (positionsSlot b t) (readingCounts.positions b t t) :=
  readGrade.map (walkPositions_grade historyOps_readGraded b t t) _

private theorem rg_fingerprintSlot : readGrade.P fingerprintSlot 5 :=
  readGrade.bind (rg_samples 4) fun _ ↦ readGrade.bind rg_sample fun _ ↦ readGrade.pure _

private theorem rg_rootsSlot : readGrade.P rootsSlot 2 :=
  readGrade.bind rg_nextScalar fun _ ↦ readGrade.bind rg_nextScalar fun _ ↦ readGrade.pure _

private theorem rg_childrenSlot (ρ : ℕ) : readGrade.P (childrenSlot ρ) (3 * 2 ^ ρ) :=
  readGrade.of_eq (readGrade.bind (rg_vecSlot _) fun _ ↦ readGrade.bind (rg_vecSlot _) fun _ ↦
    readGrade.bind (rg_vecSlot _) fun _ ↦ readGrade.pure _) (by ring)

private theorem rg_commitSlot {M : Type} (ann : List E) (w : M) :
    readGrade.P (commitSlot ann w) 10 := by
  refine readGrade.bind (k := 2) (rg_nextScalars 8) fun xs ↦ ?_
  split
  · exact readGrade.map rg_nextRoot _
  · exact rg_fail _

/-! ## The readings of leanVM's decoder, phase by phase -/

private theorem readsN_roundsDec (d : ℕ) (eq? : ℕ → Option E) (σ : Thunk E × ℕ) (m : ℕ) :
    ReadsN (roundsDec d eq? σ m) (m * (d + 1)) :=
  readsN_rounds (fun _ ↦ rg_polySlot _ _ _) (fun _ ↦ rg_sample) σ m

private theorem readsN_layerDec (st : GkrState) (ρ m : ℕ) :
    ReadsN (layerDec st ρ m) (readingCounts.layer ρ m) :=
  (readsN_append (readsN_append (readsN_append (readsN_single rg_sample)
    fun _ ↦ readsN_roundsDec _ _ _ _) fun _ ↦ readsN_single (rg_childrenSlot ρ))
    fun _ ↦ readsN_draws rg_sample ρ).of_eq
    (by simp only [StepCounts.layer, StepCounts.rounds, StepCounts.round, readingCounts]; ring)

private theorem readsN_stepsDec : ∀ (st : GkrState) (k m : ℕ),
    ReadsN (stepsDec st k m) (readingCounts.layers (List.replicate k 2) m)
  | _, 0, _ => readsN_empty
  | st, k + 1, m => (readsN_append (readsN_layerDec st 2 m)
      fun t ↦ readsN_stepsDec (layerNext t) k (m + 2)).of_eq (by
        simp only [List.replicate_succ, StepCounts.layers])

private theorem readsN_oddDec (st : GkrState) :
    ∀ r, ReadsN (oddDec st r) (if r = 0 then 0 else readingCounts.layer 1 0)
  | 0 => readsN_empty
  | _ + 1 => readsN_layerDec st 1 0

private theorem readsN_gkrDec (st : GkrState) (μ : ℕ) :
    ReadsN (gkrDec st μ) (readingCounts.layers (gkrRadices μ) 0 + 1) :=
  (readsN_append (readsN_append (readsN_oddDec st _) fun _ ↦ readsN_stepsDec _ _ _)
    fun _ ↦ readsN_single rg_sample).of_eq (by
      rcases Nat.mod_two_eq_zero_or_one μ with h | h <;>
        simp [h, gkrRadices, StepCounts.layers])

private theorem readsN_busDec (I : M3Instance) :
    ReadsN (busDec I) (readingCounts.bus I.μBus I.busClaims) :=
  (readsN_append (readsN_append (readsN_append (readsN_single rg_fingerprintSlot)
    fun _ ↦ readsN_single rg_rootsSlot) fun _ ↦ readsN_gkrDec _ _)
    fun _ ↦ readsN_single (rg_vecSlot _)).of_eq
    (by simp only [StepCounts.bus, readingCounts]; ring)

private theorem readsN_tableDec (I : M3Instance) (s : Thunk (I.Stmt × BusOut I)) :
    ReadsN (tableDec I s) (readingCounts.tables I.τmax I.tableColumns) :=
  (readsN_append (readsN_append (readsN_single rg_sample) fun _ ↦ readsN_roundsDec _ _ _ _)
    fun _ ↦ readsN_single (rg_vecSlot _)).of_eq
    (by simp only [StepCounts.tables, StepCounts.rounds, StepCounts.round, readingCounts]; ring)

private theorem readsN_pubDec (k : ℕ) : ReadsN (pubDec k) (readingCounts.pub k) := by
  intro l t r h
  obtain ⟨c, hc, hlen⟩ := run_length_of_slots (D := pubDec k)
    (g := fun j ↦ if j.val = 0 then 1 else k) (fun j tr ↦ by
      match j with
      | ⟨0, _⟩ => exact rg_sample
      | ⟨1, _⟩ => exact rg_nextScalars k) 2 le_rfl l t r h
  refine ⟨c, hc, hlen.trans ?_⟩
  simp [Fin.sum_univ_two, StepCounts.pub, readingCounts]

private theorem readsN_flockDecOf (k : ℕ) : ReadsN (flockDecOf k) (readingCounts.flock k) :=
  (readsN_append (readsN_append (readsN_append (readsN_append (readsN_append (readsN_append
    (readsN_append (readsN_append (readsN_append (readsN_draws rg_sample (k + 1))
    fun _ ↦ readsN_single (rg_vecSlot 64)) fun _ ↦ readsN_single rg_sample)
    fun _ ↦ readsN_roundsDec _ _ _ _) fun _ ↦ readsN_roundsDec _ _ _ _)
    fun _ ↦ readsN_single (rg_vecSlot 2)) fun _ ↦ readsN_single rg_sample)
    fun _ ↦ readsN_roundsDec _ _ _ _) fun _ ↦ readsN_single (rg_vecSlot 64))
    fun _ ↦ readsN_draws rg_sample 6).of_eq (by
      simp only [StepCounts.flock, StepCounts.rounds, StepCounts.round, readingCounts,
        Flock.kSkip, Flock.kIn]
      ring)

/-- The readings of the Flock slot: the Flock phase's, or none. -/
def flockReadings {I : M3Instance} : Option (FlockRegion I.toShape) → ℕ
  | none => 0
  | some r => readingCounts.flock r.kBatch

private theorem readsN_flockDec (I : M3Instance) :
    ∀ o, ReadsN (flockDec I o) (flockReadings o)
  | none => readsN_empty
  | some r => readsN_flockDecOf r.kBatch

/-- The readings of the front of the compiled protocol. -/
def frontReadings (I : M3Instance) (input : I.Stmt) : ℕ :=
  readingCounts.setup + readingCounts.bus I.μBus I.busClaims +
    readingCounts.tables I.τmax I.tableColumns +
    readingCounts.pub (PublicInput.sentCount I (I.publicLines input)) + flockReadings I.flock +
    readingCounts.sample + 0

private theorem readsN_frontDec (I : M3Instance) (h : Bus.Conditions I) (input : I.Stmt)
    (ann : List E) {sh : Whir.Shape} {κ : ℕ} (w₀ : KWord sh.ℓ (κ + sh.R) sh.t) :
    ReadsN (frontDec I h input ann w₀) (frontReadings I input) :=
  readsN_append (readsN_append (readsN_append (readsN_append (readsN_append (readsN_append
    (readsN_single (rg_commitSlot ann w₀)) fun _ ↦ readsN_busDec I) fun _ ↦ readsN_tableDec I _)
    fun _ ↦ readsN_pubDec _) fun _ ↦ readsN_flockDec I _) fun _ ↦ readsN_single rg_sample)
    fun _ ↦ readsN_empty

/-! ## Words that agree within a history -/

/-- **Later words that agree within `N` readings**, their roots at the offsets `offs`: each level's
word whose root ends within the first `N` readings. -/
def LaterAgree (N : ℕ) : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) → List ℕ → L.Words →
    L.Words → Prop
  | _, _, .last _ _, _, _, _ => True
  | _, _, @Ladder.cons _ _ _ L, offs, w, w' =>
    (∀ o, offs.head? = some o → o + 2 ≤ N → w.1 = w'.1) ∧ LaterAgree N L offs.tail w.2 w'.2

/-! ## The decoder agrees at the words it has read -/

private theorem agreeAt_levelDec (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step}
    (σ : Thunk E × Thunk (Vector E 3)) (w : WordOf sh (Kap sh' κ')) (next next' : WordOf sh' κ')
    {cont cont' : Thunk E × Thunk (Vector E 3) → SeqDecoder Reading k} {p N : ℕ}
    (hnext : next = next' ∨ N < p + readingCounts.folds sh.ℓ + 2)
    (hcont : ∀ τ, AgreeAt (cont τ).toDecoder (cont' τ).toDecoder
      (p + readingCounts.level (levelShape sh sh' κ')) N) :
    AgreeAt (levelDec sh sh' κ' σ w next cont).toDecoder
      (levelDec sh sh' κ' σ w next' cont').toDecoder p N := by
  dsimp only [levelDec, SeqDecoder.toDecoder]
  refine agreeAt_append (agreeAt_refl _ _ _) (readsN_single rg_sample) fun _ ↦
    agreeAt_append (agreeAt_refl _ _ _) (readsN_roundsDec _ _ _ _) fun _ ↦
    agreeAt_append (agreeAt_refl _ _ _) (readsN_single (rg_polySlot _ _ _)) fun _ ↦
    agreeAt_append (agreeAt_single fun r hr ↦ ?_) (readsN_single (readGrade.map rg_nextRoot _))
      fun _ ↦
    agreeAt_append (agreeAt_refl _ _ _) (readsN_draws rg_sample _) fun _ ↦
    agreeAt_append (agreeAt_refl _ _ _) (readsN_single rg_nextScalar) fun _ ↦
    agreeAt_append (agreeAt_refl _ _ _) (readsN_single (rg_polySlot _ _ _)) fun _ ↦
    agreeAt_append (agreeAt_refl _ _ _) (readsN_single (rg_checkPow _)) fun _ ↦
    agreeAt_append (agreeAt_refl _ _ _) (readsN_single (rg_positionsSlot _ _)) fun _ ↦
    agreeAt_append (agreeAt_refl _ _ _) (readsN_single rg_sample) fun _ ↦
    agreeAt_append (agreeAt_refl _ _ _) readsN_empty fun _ ↦
    agreeAt_append (agreeAt_refl _ _ _) (readsN_single (rg_polySlot _ _ _)) fun _ ↦
    agreeAt_append (agreeAt_refl _ _ _) readsN_empty fun _ ↦ (hcont _).of_eq ?_
  · rcases hnext with rfl | hlt
    · rfl
    · have hr2 : r.length < 2 := by
        norm_num [StepCounts.folds, readingCounts, Whir.Shape.ℓ] at hlt hr
        omega
      exact (read_eq_none_of_lt (readGrade.map rg_nextRoot _) hr2).trans
        (read_eq_none_of_lt (readGrade.map rg_nextRoot _) hr2).symm
  · simp only [StepCounts.level, StepCounts.folds, readingCounts, Step.n, Kap,
      Bool.false_eq_true, ↓reduceIte]
    ring

private theorem agreeAt_ladderDec : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (σ : Thunk E × Thunk (Vector E 3)) (w : WordOf sh κ) (ws ws' : L.Words) {p N : ℕ},
    LaterAgree N L (levelRootOffsets readingCounts p L.shapes) ws ws' →
    AgreeAt (ladderDec L σ w ws).toDecoder (ladderDec L σ w ws').toDecoder p N
  | _, _, .last _ _, _, _, _, _, _, _, _ => agreeAt_refl _ _ _
  | _, _, @Ladder.cons sh sh' κ' L, σ, w, ws, ws', p, N, h => by
    have hnext : ws.1 = ws'.1 ∨ N < p + readingCounts.folds sh.ℓ + 2 := by
      by_cases hN : p + readingCounts.folds sh.ℓ + 2 ≤ N
      · exact .inl (h.1 _ rfl hN)
      · exact .inr (by omega)
    refine agreeAt_levelDec sh sh' κ' σ w ws.1 ws'.1 hnext fun τ ↦ ?_
    rcases hnext with he | hlt
    · rw [he]
      exact agreeAt_ladderDec L τ ws'.1 ws.2 ws'.2 h.2
    · refine agreeAt_of_lt ?_
      simp only [StepCounts.level, StepCounts.folds, readingCounts, Bool.false_eq_true,
        ↓reduceIte] at hlt ⊢
      omega

private theorem agreeAt_whirDec {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (target : Thunk E)
    (w : WordOf sh κ) (ws ws' : L.Words) {p N : ℕ}
    (h : LaterAgree N L (levelRootOffsets readingCounts (p + 2) L.shapes) ws ws') :
    AgreeAt (whirDec L target w ws).toDecoder (whirDec L target w ws').toDecoder p N := by
  dsimp only [whirDec, SeqDecoder.toDecoder]
  exact agreeAt_append (agreeAt_refl _ _ _) readsN_empty fun _ ↦
    agreeAt_append (agreeAt_refl _ _ _) (readsN_single (rg_polySlot _ _ _)) fun _ ↦
      (agreeAt_ladderDec L _ w ws ws' h).of_eq (by omega)

/-- **The compiled decoder agrees** at words that agree on every word whose root lies within the
history: the level-0 word, read with the commitment's root at readings `8` and `9`, and each later
level's, its root at the reading offset after the front and the levels before it. -/
theorem agreeAt_compiledDec (I : M3Instance) (hI : Bus.Conditions I) (input : I.Stmt)
    (ann : List E) (c : Chain) (W W' : Words c) {N : ℕ} (h0 : 10 ≤ N → W.level0 = W'.level0)
    (hL : LaterAgree N c.ladder
      (levelRootOffsets readingCounts (frontReadings I input + 2) c.ladder.shapes) W.later
      W'.later) :
    AgreeAt (compiledDec I hI input ann c W) (compiledDec I hI input ann c W') 0 N := by
  have hF : 10 ≤ frontReadings I input := by
    simp only [frontReadings, StepCounts.setup, readingCounts]
    omega
  dsimp only [compiledDec, frontDec]
  refine agreeAt_append (agreeAt_append_same (agreeAt_append_same (agreeAt_append_same
    (agreeAt_append_same (agreeAt_append_same (agreeAt_append_same
      (agreeAt_single fun r hr ↦ ?_)))))))
    (readsN_frontDec I hI input ann W.level0) fun t ↦ ?_
  · by_cases h10 : 10 ≤ N
    · rw [h0 h10]
    · rw [read_eq_none_of_lt (rg_commitSlot _ _) (by omega),
        read_eq_none_of_lt (rg_commitSlot _ _) (by omega)]
  · by_cases h10 : 10 ≤ N
    · rw [h0 h10]
      exact agreeAt_whirDec c.ladder _ _ _ _ ((show frontReadings I input + 2 =
        0 + frontReadings I input + 2 by omega) ▸ hL)
    · exact agreeAt_of_lt (by omega)

/-! ## At leanVM -/

section Deployed

variable (prog : Program) (input : PublicInput) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
  (hρ : validRate ρ)

/-- **Words that agree within a history of `N` readings**: the level-0 word when the commitment's
root, readings `8` and `9`, lies within them, and each later level's word when its root, at its
reading offset (`rootOffsets readingCounts`), does. -/
def WordsAgree (N : ℕ) (W W' : LeanWords prog s hs ρ hρ) : Prop :=
  (10 ≤ N → W.level0 = W'.level0) ∧
    LaterAgree N (leanIsaChain prog s hs ρ hρ).ladder
      (levelRootOffsets readingCounts (whirStart readingCounts prog s input)
        (leanIsaChain prog s hs ρ hρ).ladder.shapes) W.later W'.later

/-- WHIR starts where the front of the decoder ends, after the first round polynomial. -/
private theorem whirStart_eq_frontReadings :
    whirStart readingCounts prog s input = frontReadings (leanVm prog s) input + 2 := by
  simp only [whirStart, frontReadings, flockReadings, readingCounts]
  rfl

variable {prog input s hs ρ hρ}

/-- **A history decodes alike with words that agree on its roots**: decoders whose words agree on
every word whose root lies within the history decode the same prefix of the transcript off it. -/
theorem decodePrefix_words_congr {W W' : LeanWords prog s hs ρ hρ} {hist : List Reading}
    (h : WordsAgree prog input s hs ρ hρ hist.length W W') :
    DecodeChain.decodePrefix prog input s hs ρ hρ W hist =
      DecodeChain.decodePrefix prog input s hs ρ hρ W' hist := by
  unfold DecodeChain.decodePrefix decoder
  refine decodePrefix_congr ((agreeAt_compiledDec _ _ _ _ _ W W' h.1 ?_).run (Nat.zero_add _))
  rw [← whirStart_eq_frontReadings]
  exact h.2

/-- **A prefix decodes to the prefix of the decode**: with one family of words, the transcript
prefix a history's prefix decodes to is the decoded transcript's first rounds. -/
theorem decodePrefix_take {W : LeanWords prog s hs ρ hρ} {hist rest : List Reading}
    {t : (deployedSpec Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ).FullTranscript}
    {i : Fin _} {tr : (deployedSpec Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ).Transcript i}
    (ht : DecodeChain.decode prog input s hs ρ hρ W (hist ++ rest) = some t)
    (h : DecodeChain.decodePrefix prog input s hs ρ hρ W hist = some ⟨i, tr⟩) :
    FullTranscript.take i.val i.is_le t = tr :=
  (decoder prog input s hs ρ hρ W).decode_eq_of_decodePrefix ht h

end Deployed

end DecodeAgree

end

end LeanerVM.Protocol
