/-
  LeanerVM.Protocol.Core.Flip

  A challenge of the verifier's decoded history that is bad at the prefix before it makes its
  group of squeezes flip in the log.
-/

module

public import LeanerVM.Protocol.LeanVmReader
public import LeanerVM.Protocol.ToArkLib.StateWalk

/-!
# A bad challenge flips its group

The verifier's chain history decodes to a transcript of the compiled protocol. Each challenge of
that transcript is read off a run of squeezes, its digests assembled by the challenge's slot.
The decoder's challenge rounds read squeezes alone (`SqueezesOnly`, round by round down to the
leaves of the compiled decoder), and a challenge slot that reads squeezes alone and reads its
squeezes when they come first reads exactly them (`read_eq_squeezes`). So a challenge sits in
the history after a prefix the decoder reads exactly to it, its squeezes next
(`challenge_cut`).

`SlotReader.flipAt_of_decoder`, for any reader whose prefixes are a decoder's: on a log with no
collision, holding every step of the history from a start that opens a statement, its later states
no starts, if a challenge of the decoded transcript is bad at the prefix before it
(`SlotReader.BadIn`), its group flips in the log: the group of its nonce when a grinding nonce
precedes it, whose proof of work the log passes, and the group of its state otherwise. The group's
history is the prefix, by the chain's injectivity on the log, and the prefix decodes with the
words its own roots give.
`flipAt_of_bad` is its instance at leanVM's reader, from the statement's seed on a log where no
answer is the seed, on a transcript of the compiled protocol.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa ProtocolSpec StepSchedule Verify
open DecodeChain Whir SlotDecoder ProofRoots LeanVmSlots

@[expose] public section

namespace Core

-- The stack's size is never computed here: sealed, unification does not evaluate it on a
-- symbolic program.
attribute [local irreducible] LeanIsa.leanIsaμ LeanIsa.blocks

/-! ## Challenges read squeezes alone -/

/-- A slot reads squeezes alone: what it consumes is a run of squeezes. -/
private def ReadsOnlySqueezes {β : Type} (s : Slot Reading β) : Prop :=
  ∀ l x r, s.read l = some (x, r) → ∃ ds, l = squeezeBlocks ds ++ r

private theorem ReadsOnlySqueezes.pure {β : Type} (x : β) :
    ReadsOnlySqueezes (Pure.pure x : Slot Reading β) := by
  intro l y r h
  rw [Slot.read_pure, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨[], by simp [squeezeBlocks, h.2]⟩

private theorem ReadsOnlySqueezes.bind {β γ : Type} {s : Slot Reading β} {f : β → Slot Reading γ}
    (hs : ReadsOnlySqueezes s) (hf : ∀ x, ReadsOnlySqueezes (f x)) :
    ReadsOnlySqueezes (s >>= f) := by
  intro l y r h
  rw [Slot.read_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨x, l₁⟩, h₁, h₂⟩ := h
  obtain ⟨ds₁, rfl⟩ := hs _ _ _ h₁
  obtain ⟨ds₂, rfl⟩ := hf x _ _ _ h₂
  exact ⟨ds₁ ++ ds₂, by simp [squeezeBlocks]⟩

private theorem ReadsOnlySqueezes.map {β γ : Type} {s : Slot Reading β} (hs : ReadsOnlySqueezes s)
    (g : β → γ) : ReadsOnlySqueezes (g <$> s) := by
  rw [← bind_pure_comp]
  exact hs.bind fun _ ↦ .pure _

private theorem ReadsOnlySqueezes.slotMap {β γ : Type} {s : Slot Reading β}
    (hs : ReadsOnlySqueezes s)
    (g : β → γ) : ReadsOnlySqueezes (s.map g) := by
  intro l y r h
  obtain ⟨⟨x, r'⟩, hx, he⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨-, rfl⟩ := Prod.mk.inj he
  exact hs _ _ _ hx

private theorem readsOnlySqueezes_sample : ReadsOnlySqueezes historyOps.sample := by
  rintro (_ | ⟨⟨b, d⟩, l⟩) x r h
  · exact nomatch h
  · change (challengeOf (b, d)).map (·, l) = some (x, r) at h
    cases b with
    | squeeze =>
      simp only [challengeOf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨[d], by simp [squeezeBlocks, h.2]⟩
    | observe _ => simp [challengeOf] at h
    | nonce _ => simp [challengeOf] at h

private theorem readsOnlySqueezes_samples : ∀ k, ReadsOnlySqueezes (samples historyOps k)
  | 0 => .pure _
  | k + 1 => readsOnlySqueezes_sample.bind fun _ ↦
      (readsOnlySqueezes_samples k).bind fun _ ↦ .pure _

private theorem readsOnlySqueezes_positionsWith (depth : ℕ) :
    ∀ fuel need, ReadsOnlySqueezes (positionsWith historyOps.sample depth fuel need)
  | 0, _ => .pure _
  | _ + 1, 0 => .pure _
  | fuel + 1, need + 1 => by
    rw [positionsWith]
    exact readsOnlySqueezes_sample.bind fun _ ↦
      (readsOnlySqueezes_positionsWith depth fuel _).bind fun _ ↦ .pure _

private theorem readsOnlySqueezes_positionsSlot (b t : ℕ) : ReadsOnlySqueezes (positionsSlot b t) :=
  (readsOnlySqueezes_positionsWith _ _ _).map _

private theorem readsOnlySqueezes_fingerprintSlot : ReadsOnlySqueezes fingerprintSlot :=
  (readsOnlySqueezes_samples 4).bind fun _ ↦ readsOnlySqueezes_sample.bind fun _ ↦ .pure _

private theorem ofFn_getElem' {α : Type} {l : List α} {m : ℕ} (h : l.length = m) :
    List.ofFn (fun i : Fin m ↦ l[i.1]'(h ▸ i.2)) = l := by
  apply List.ext_getElem (by simp [h])
  intro i h₁ h₂
  simp

private theorem squeezeBlocks_append (a b : List Digest) :
    squeezeBlocks (a ++ b) = squeezeBlocks a ++ squeezeBlocks b := by
  simp [squeezeBlocks]

private theorem squeezeBlocks_eq_nil {a : List Digest} (h : squeezeBlocks a = []) : a = [] := by
  simpa [squeezeBlocks] using h

/-- A challenge slot that reads squeezes alone, and its squeezes when they come first, reads
exactly its squeezes. -/
private theorem read_eq_squeezes {C : Type} {s : Slot Reading C} {u : UniformSlot C}
    (hs : ReadsSqueezes s u) (ho : ReadsOnlySqueezes s) {l : List Reading}
    {x : C} {r : List Reading} (h : s.read l = some (x, r)) :
    ∃ ds : Fin u.m → Digest, l = squeezeBlocks (List.ofFn ds) ++ r ∧ x = u.assemble ds := by
  obtain ⟨ds, rfl⟩ := ho _ _ _ h
  have hc : s.read (squeezeBlocks ds) = some (x, []) := by
    obtain ⟨c, hc, hr⟩ := s.read_iff.mp h
    rwa [List.append_cancel_right hc]
  have hlen : ds.length = u.m := by
    rcases Nat.lt_trichotomy ds.length u.m with hlt | heq | hgt
    · exfalso
      have hl : (ds ++ List.replicate (u.m - ds.length) (default : Digest)).length = u.m := by
        simp only [List.length_append, List.length_replicate]
        omega
      have h₁ := hs (fun i ↦ (ds ++ List.replicate (u.m - ds.length) default)[i.1]'(by omega)) []
      rw [ofFn_getElem' hl, List.append_nil, squeezeBlocks_append] at h₁
      have h₂ := s.read_append hc (squeezeBlocks (List.replicate (u.m - ds.length) default))
      rw [List.nil_append, h₁] at h₂
      have h₃ := squeezeBlocks_eq_nil (Prod.mk.inj (Option.some.inj h₂)).2.symm
      simp only [List.replicate_eq_nil_iff] at h₃
      omega
    · exact heq
    · exfalso
      have hl : (ds.take u.m).length = u.m := by simp only [List.length_take]; omega
      have h₁ := hs (fun i ↦ (ds.take u.m)[i.1]'(by omega))
        (squeezeBlocks (ds.drop u.m) ++ r)
      rw [ofFn_getElem' hl, ← List.append_assoc, ← squeezeBlocks_append, List.take_append_drop,
        h] at h₁
      have h₃ := (Prod.mk.inj (Option.some.inj h₁)).2
      have h₄ : squeezeBlocks (ds.drop u.m) = [] := by
        have := congrArg List.length h₃
        simp only [List.length_append] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      have h₅ := congrArg List.length (squeezeBlocks_eq_nil h₄)
      simp only [List.length_drop, List.length_nil] at h₅
      omega
  refine ⟨fun i ↦ ds[i.1]'(by omega), by rw [ofFn_getElem' hlen], ?_⟩
  have h₁ := hs (fun i ↦ ds[i.1]'(by omega)) r
  rw [ofFn_getElem' hlen, h] at h₁
  exact (Prod.mk.inj (Option.some.inj h₁)).1

/-! ## Decoders whose challenges read squeezes alone -/

section Decoders

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- Every challenge round of a decoder reads squeezes alone. -/
private def SqueezesOnly (D : SlotDecoder Reading pSpec) : Prop :=
  ∀ (k : Fin n) (_ : pSpec.dir k = .V_to_P) (tr : pSpec.Transcript k.castSucc),
    ReadsOnlySqueezes (D.slot k tr)

private theorem squeezesOnly_empty {pSpec : ProtocolSpec 0} : SqueezesOnly
    (empty : SlotDecoder Reading pSpec) :=
  fun k ↦ k.elim0

private theorem squeezesOnly_say {M : Type} (s : Slot Reading M) : SqueezesOnly (single
    (pSpec := say M) s) :=
  fun ⟨0, _⟩ h ↦ nomatch h

private theorem squeezesOnly_sayO {M : Type} [OracleInterface M] (s : Slot Reading M) :
    SqueezesOnly (single (pSpec := Component.sayO M) s) :=
  fun ⟨0, _⟩ h ↦ nomatch h

private theorem squeezesOnly_draw {C : Type} {s : Slot Reading C} (hs : ReadsOnlySqueezes s) :
    SqueezesOnly (single (pSpec := draw C) s) :=
  fun ⟨0, _⟩ _ _ ↦ hs

private theorem squeezesOnly_append {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {D₁ : SlotDecoder Reading pSpec₁} {D₂ : pSpec₁.FullTranscript → SlotDecoder Reading pSpec₂}
    (h₁ : SqueezesOnly D₁) (h₂ : ∀ t, SqueezesOnly (D₂ t)) : SqueezesOnly (D₁.append D₂) := by
  rintro ⟨k, hk⟩ hd tr
  by_cases hkm : k < m
  · rw [append_slot_left D₁ D₂ k hkm hk tr]
    exact (h₁ _ (by rw [← append_dir_castAdd (pSpec₂ := pSpec₂) ⟨k, hkm⟩]; exact hd) _).slotMap _
  · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
    rw [append_slot_right D₁ D₂ j (by omega) hk tr]
    exact (h₂ _ _ (by rw [← append_dir_natAdd (pSpec₁ := pSpec₁)
      ⟨j, by omega⟩]; exact hd) _).slotMap _

private theorem squeezesOnly_draws {C : Type} {s : Slot Reading C} (hs : ReadsOnlySqueezes s) :
    ∀ k, SqueezesOnly (SlotDecoder.draws s k)
  | 0 => squeezesOnly_empty
  | k + 1 => squeezesOnly_append (D₁ := SlotDecoder.draws s k) (squeezesOnly_draws hs k)
      fun _ ↦ squeezesOnly_draw hs

private theorem squeezesOnly_rounds {C σ : Type} {d : ℕ} {poly : σ → Slot Reading (Vector C
    (d + 1))}
    {chal : σ → Slot Reading C} {next : σ → (roundSpec C d).FullTranscript → σ}
    (hc : ∀ a, ReadsOnlySqueezes (chal a)) :
    ∀ (a : σ) (m : ℕ), SqueezesOnly (rounds poly chal next a m)
  | _, 0 => squeezesOnly_empty
  | a, m + 1 => squeezesOnly_append (squeezesOnly_append
    (squeezesOnly_say _) fun _ ↦ squeezesOnly_draw (hc a))
      fun t ↦ squeezesOnly_rounds hc (next a t) m

/-- Every step of a list reads squeezes alone at its challenges. -/
private def SeqSqueezesOnly : {l : List Step} → SeqDecoder Reading l → Prop
  | [], _ => True
  | _ :: _, D => SqueezesOnly D.1 ∧ ∀ t, SeqSqueezesOnly (D.2 t)

private theorem SeqSqueezesOnly.toDecoder : ∀ {l : List Step}
    {D : SeqDecoder Reading l}, SeqSqueezesOnly D →
    SqueezesOnly D.toDecoder
  | [], _, _ => squeezesOnly_empty
  | _ :: _, _, h => squeezesOnly_append h.1 fun t ↦ (h.2 t).toDecoder

end Decoders

/-! ## At leanVM -/

private theorem squeezesOnly_roundsDec (d : ℕ) (eq? : ℕ → Option E) (σ : Thunk E × ℕ) (m : ℕ) :
    SqueezesOnly (roundsDec d eq? σ m) :=
  squeezesOnly_rounds (fun _ ↦ readsOnlySqueezes_sample) σ m

private theorem squeezesOnly_layerDec (st : GkrState) (ρ m : ℕ) : SqueezesOnly (layerDec st ρ m) :=
  squeezesOnly_append (squeezesOnly_append (squeezesOnly_append
    (squeezesOnly_draw readsOnlySqueezes_sample)
    fun _ ↦ squeezesOnly_roundsDec _ _ _ _) fun _ ↦ squeezesOnly_say _)
    fun _ ↦ squeezesOnly_draws readsOnlySqueezes_sample ρ

private theorem squeezesOnly_stepsDec : ∀ (st : GkrState) (k m : ℕ), SqueezesOnly (stepsDec st k m)
  | _, 0, _ => squeezesOnly_empty
  | st, k + 1, m => squeezesOnly_append (squeezesOnly_layerDec st 2 m)
      fun t ↦ squeezesOnly_stepsDec (layerNext t) k (m + 2)

private theorem squeezesOnly_oddDec (st : GkrState) : ∀ r, SqueezesOnly (oddDec st r)
  | 0 => squeezesOnly_empty
  | _ + 1 => squeezesOnly_layerDec st 1 0

private theorem squeezesOnly_gkrDec (st : GkrState) (μ : ℕ) : SqueezesOnly (gkrDec st μ) :=
  squeezesOnly_append (squeezesOnly_append
    (squeezesOnly_oddDec st _) fun _ ↦ squeezesOnly_stepsDec _ _ _)
    fun _ ↦ squeezesOnly_draw readsOnlySqueezes_sample

private theorem squeezesOnly_busDec (I : M3Instance) : SqueezesOnly (busDec I) :=
  squeezesOnly_append (squeezesOnly_append (squeezesOnly_append
    (squeezesOnly_draw readsOnlySqueezes_fingerprintSlot)
    fun _ ↦ squeezesOnly_say _) fun _ ↦ squeezesOnly_gkrDec _ _) fun _ ↦ squeezesOnly_say _

private theorem squeezesOnly_tableDec (I : M3Instance) (s : Thunk (I.Stmt × BusOut I)) :
    SqueezesOnly (tableDec I s) :=
  squeezesOnly_append (squeezesOnly_append (squeezesOnly_draw readsOnlySqueezes_sample)
    fun _ ↦ squeezesOnly_roundsDec _ _ _ _) fun _ ↦ squeezesOnly_say _

private theorem squeezesOnly_pubDec (n : ℕ) : SqueezesOnly (pubDec n)
  | ⟨0, _⟩, _, _ => readsOnlySqueezes_sample
  | ⟨1, _⟩, h, _ => nomatch h

private theorem squeezesOnly_flockDecOf (k : ℕ) : SqueezesOnly (flockDecOf k) := by
  unfold flockDecOf
  exact squeezesOnly_append (squeezesOnly_append (squeezesOnly_append (squeezesOnly_append
    (squeezesOnly_append
    (squeezesOnly_append (squeezesOnly_append (squeezesOnly_append (squeezesOnly_append
    (squeezesOnly_draws readsOnlySqueezes_sample _) fun _ ↦ squeezesOnly_say _)
    fun _ ↦ squeezesOnly_draw readsOnlySqueezes_sample) fun _ ↦ squeezesOnly_roundsDec _ _ _ _)
    fun _ ↦ squeezesOnly_roundsDec _ _ _ _) fun _ ↦ squeezesOnly_say _)
    fun _ ↦ squeezesOnly_draw readsOnlySqueezes_sample) fun _ ↦ squeezesOnly_roundsDec _ _ _ _)
    fun _ ↦ squeezesOnly_say _) fun _ ↦ squeezesOnly_draws readsOnlySqueezes_sample _

private theorem squeezesOnly_flockDec (I : M3Instance) : ∀ o, SqueezesOnly (flockDec I o)
  | none => squeezesOnly_empty
  | some r => squeezesOnly_flockDecOf r.kBatch

private theorem squeezesOnly_frontDec (I : M3Instance) (h : Bus.Conditions I) (input : I.Stmt)
    (ann : List E)
    {sh : Whir.Shape} {κ : ℕ} (w₀ : KWord sh.ℓ (κ + sh.R) sh.t) :
    SqueezesOnly (frontDec I h input ann w₀) :=
  squeezesOnly_append (squeezesOnly_append (squeezesOnly_append (squeezesOnly_append
    (squeezesOnly_append (squeezesOnly_append
    (fun ⟨0, _⟩ h ↦ nomatch h) fun _ ↦ squeezesOnly_busDec I) fun _ ↦ squeezesOnly_tableDec I _)
    fun _ ↦ squeezesOnly_pubDec _) fun _ ↦ squeezesOnly_flockDec I _)
    fun _ ↦ squeezesOnly_draw readsOnlySqueezes_sample) fun _ ↦ squeezesOnly_empty

private theorem squeezesOnly_levelDec (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step}
    (σ : Thunk E × Thunk (Vector E 3)) (w : WordOf sh (Kap sh' κ')) (next : WordOf sh' κ')
    {cont : Thunk E × Thunk (Vector E 3) → SeqDecoder Reading k}
    (hc : ∀ σ', SeqSqueezesOnly (cont σ')) : SeqSqueezesOnly
      (levelDec sh sh' κ' σ w next cont) := by
  dsimp only [levelDec]
  exact ⟨squeezesOnly_draw readsOnlySqueezes_sample, fun _ ↦
    ⟨squeezesOnly_roundsDec 2 (fun _ ↦ none) _ sh.lm1, fun _ ↦
    ⟨squeezesOnly_say _, fun _ ↦
    ⟨squeezesOnly_sayO _, fun _ ↦
    ⟨squeezesOnly_draws readsOnlySqueezes_sample _, fun _ ↦
    ⟨squeezesOnly_say _, fun _ ↦
    ⟨squeezesOnly_say _, fun _ ↦
    ⟨squeezesOnly_say _, fun _ ↦
    ⟨squeezesOnly_draw (readsOnlySqueezes_positionsSlot _ _), fun _ ↦
    ⟨squeezesOnly_draw readsOnlySqueezes_sample, fun _ ↦
    ⟨squeezesOnly_empty, fun _ ↦
    ⟨squeezesOnly_say _, fun _ ↦
    ⟨squeezesOnly_empty, fun _ ↦ hc _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem squeezesOnly_finalDec (sh : Whir.Shape) (nf : ℕ) (σ : Thunk E × Thunk (Vector E 3))
    (w : WordOf sh (nf + 1)) : SeqSqueezesOnly (finalDec sh nf σ w) := by
  dsimp only [finalDec]
  exact ⟨squeezesOnly_draw readsOnlySqueezes_sample, fun _ ↦
    ⟨squeezesOnly_roundsDec 2 (fun _ ↦ none) _ sh.lm1, fun _ ↦
    ⟨squeezesOnly_say _, fun _ ↦
    ⟨squeezesOnly_say _, fun _ ↦
    ⟨squeezesOnly_say _, fun _ ↦
    ⟨squeezesOnly_draw (readsOnlySqueezes_positionsSlot _ _), fun _ ↦
    ⟨squeezesOnly_draw readsOnlySqueezes_sample, fun _ ↦
    ⟨squeezesOnly_empty, fun _ ↦
    ⟨squeezesOnly_say _, fun _ ↦
    ⟨squeezesOnly_empty, fun _ ↦
    ⟨squeezesOnly_draw readsOnlySqueezes_sample, fun _ ↦
    ⟨squeezesOnly_roundsDec 2 (fun _ ↦ none) _ nf, fun _ ↦ trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem squeezesOnly_ladderDec : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (σ : Thunk E × Thunk (Vector E 3)) (w : WordOf sh κ) (ws : L.Words),
    SeqSqueezesOnly (ladderDec L σ w ws)
  | _, _, .last sh nf, σ, w, _ => squeezesOnly_finalDec sh nf σ w
  | _, _, @Ladder.cons sh sh' κ' L, σ, w, ws =>
    squeezesOnly_levelDec sh sh' κ' σ w ws.1 fun σ' ↦ squeezesOnly_ladderDec L σ' ws.1 ws.2

/-- **The compiled decoder's challenges read squeezes alone.** -/
private theorem squeezesOnly_compiledDec (I : M3Instance) (hI : Bus.Conditions I) (input : I.Stmt)
    (ann : List E) (c : Chain) (W : Words c) : SqueezesOnly (compiledDec I hI input ann c W) :=
  squeezesOnly_append (squeezesOnly_frontDec I hI input ann W.level0) fun _ ↦
    SeqSqueezesOnly.toDecoder ⟨squeezesOnly_empty, fun _ ↦ ⟨squeezesOnly_say _, fun _ ↦
      squeezesOnly_ladderDec c.ladder _ _ _⟩⟩


/-! ## Where a challenge sits in a decoded history -/

section Cut

variable {n : ℕ} {pSpec : ProtocolSpec n}

private theorem run_succ_eq_some {D : SlotDecoder Reading pSpec} {j : ℕ} {hj : j + 1 ≤ n}
    {l : List Reading} {tr : pSpec.Transcript ⟨j + 1, by omega⟩} {r : List Reading}
    (h : D.run (j + 1) hj l = some (tr, r)) :
    ∃ t l₁ x, D.run j (by omega) l = some (t, l₁) ∧ (D.slot ⟨j, hj⟩ t).read l₁ = some (x, r) ∧
      tr = Transcript.concat (m := ⟨j, hj⟩) x t := by
  simp only [SlotDecoder.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨t, l₁⟩, ht, ⟨x, r'⟩, hx, he⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact ⟨t, l₁, x, ht, hx, rfl⟩

private theorem take_succ_eq_concat (full : pSpec.FullTranscript) (j : Fin n) :
    full.take j.succ.val j.succ.is_le =
      Transcript.concat (full j) (full.take j.val j.castSucc.is_le) :=
  Fin.take_succ_eq_snoc j.val j.isLt full

/-- **Where a challenge sits in a decoded history**: before it, a prefix the decoder reads
exactly to the challenge; then its squeezes, whose digests give it; then the rest. -/
private theorem challenge_cut {D : SlotDecoder Reading pSpec} {f : ChalSlots pSpec}
    (hS : SqueezeReads D f) (hO : SqueezesOnly D) (hP : f.Pos) {l : List Reading}
    {t : pSpec.FullTranscript} (hdec : D.decode l = some t) (i : pSpec.ChallengeIdx) :
    ∃ (c : List Reading) (ds : Fin (f i.1 i.2).m → Digest) (rest : List Reading),
      l = c ++ (squeezeBlocks (List.ofFn ds) ++ rest) ∧
      D.decodePrefix c = some ⟨i.1.castSucc, t.take i.1.val i.1.castSucc.is_le⟩ ∧
      t i.1 = (f i.1 i.2).assemble ds := by
  have hfull := D.decode_eq_some.mp hdec
  obtain ⟨r₁, hr₁⟩ := D.run_take hfull (i.1.val + 1) i.1.isLt
  obtain ⟨tp, rest₀, x, hp, hx, he⟩ := run_succ_eq_some hr₁
  obtain ⟨r₂, hr₂⟩ := D.run_take hfull i.1.val (Nat.le_of_lt i.1.isLt)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hp.symm.trans hr₂))
  have hxt : x = t i.1 := by
    have h₁ := take_succ_eq_concat t i.1
    have h₂ : Transcript.concat (m := i.1) x (t.take i.1.val i.1.castSucc.is_le) =
        Transcript.concat (m := i.1) (t i.1) (t.take i.1.val i.1.castSucc.is_le) :=
      he.symm.trans h₁
    have := congrArg (fun T ↦ T (Fin.last i.1.val)) h₂
    simp only [Transcript.concat_last] at this
    exact this
  subst hxt
  obtain ⟨ds, hrest, hds⟩ := read_eq_squeezes (hS i.1 i.2 _) (hO i.1 i.2 _) hx
  obtain ⟨c, hl, hc⟩ := D.run_eq_some_iff.mp hp
  refine ⟨c, ds, r₁, by rw [hl, hrest], D.decodePrefix_eq_some_iff.mpr
    ⟨D.decodeAt_eq_some.mpr hc, fun j hj ↦ ?_⟩, hds⟩
  rcases hdj : D.decodeAt j c with _ | t'
  · rfl
  exfalso
  have hrj := D.decodeAt_eq_some.mp hdj
  obtain ⟨r₃, hr₃⟩ := D.run_take hrj (i.1.val + 1)
    (by simp only [Fin.lt_def, Fin.val_castSucc] at hj; omega)
  obtain ⟨tp', rest', x', hp', hx', -⟩ := run_succ_eq_some hr₃
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hp'.symm.trans hc))
  obtain ⟨ds', hnil, -⟩ := read_eq_squeezes (hS i.1 i.2 _) (hO i.1 i.2 _) hx'
  have h₀ := congrArg List.length hnil
  simp only [List.length_nil, List.length_append, squeezeBlocks, List.length_map,
    List.length_ofFn] at h₀
  have := hP i.1 i.2
  omega

end Cut

/-! ## The squeezes of a chain in a log -/

private theorem squeezeRun_of_chain {l : hashSpec.QueryLog} (hc : QueryLog.Consistent l) :
    ∀ (x : Digest) (ds : List Digest),
      (∀ e ∈ HashChain.queries Block.input x (squeezeBlocks ds), e ∈ l) →
      squeezeRun l x ds.length = ds
  | _, [], _ => rfl
  | x, d :: ds, h => by
    have h₁ : MerkleTree.logAnswer l (squeezeInput x) = some d :=
      logAnswer_of_consistent hc (e := ⟨Block.input x .squeeze, d⟩)
        (h _ (by simp [squeezeBlocks, HashChain.queries]))
    simp only [List.length_cons, squeezeRun, h₁]
    rw [squeezeRun_of_chain hc d ds fun e he ↦ h e (by
      simp only [squeezeBlocks, List.map_cons, HashChain.queries, List.mem_cons] at he ⊢
      exact Or.inr he)]

/-! ## A nonce step carries no root -/

private theorem rootAt_eq_none {hist : List Reading} {o : ℕ}
    (h : ∀ x d, hist[o + 1]? ≠ some (.observe x, d)) : rootAt hist o = none := by
  unfold rootAt
  split <;> simp_all

private theorem rootAt_append_nonce (hs : List Reading) (n : E) (d : Digest) (o : ℕ) :
    rootAt (hs ++ [(.nonce n, d)]) o = rootAt hs o := by
  rcases Nat.lt_or_ge (o + 1) hs.length with h | h
  · exact rootAt_prefix hs _ h
  · have h₁ : rootAt hs o = none := rootAt_eq_none fun x d' h' ↦ by
      rw [List.getElem?_eq_none (by omega)] at h'
      cases h'
    have h₂ : rootAt (hs ++ [(.nonce n, d)]) o = none := rootAt_eq_none fun x d' h' ↦ by
      rw [List.getElem?_append_right (by omega)] at h'
      rcases hk : o + 1 - hs.length with _ | k <;> simp [hk] at h'
    rw [h₁, h₂]

private theorem wordsOf_append_nonce (prog : Program) (input : PublicInput) (s : Sizes)
    (hs : s.Admissible prog) (ρ : ℕ) (hρ : validRate ρ) (l : hashSpec.QueryLog)
    (hist : List Reading) (n : E) (d : Digest) :
    LeanVmReader.wordsOf prog input s hs ρ hρ l (hist ++ [(.nonce n, d)]) =
      LeanVmReader.wordsOf prog input s hs ρ hρ l hist := by
  have h : rootAt (hist ++ [(.nonce n, d)]) = rootAt hist := funext (rootAt_append_nonce hist n d)
  simp only [LeanVmReader.wordsOf, h]

/-! ## A bad challenge flips its group -/

private theorem getElem?_cut {c rest : List Reading} {m : ℕ} (hm : 0 < m) (ds : Fin m → Digest) :
    (c ++ (squeezeBlocks (List.ofFn ds) ++ rest))[c.length]? = some (.squeeze, ds ⟨0, hm⟩) := by
  rw [List.getElem?_append_right le_rfl, Nat.sub_self]
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp [squeezeBlocks, List.ofFn_succ]

/-- The challenge a transcript carries at `i` is bad at the prefix before it. -/
def _root_.LeanerVM.Protocol.SlotReader.BadIn (R : SlotReader) {a : R.Ann}
    (tr : (R.spec a).FullTranscript) (i : (R.spec a).ChallengeIdx) : Prop :=
  challengeAt tr i ∈ R.Bad a i (prefixBefore tr i)

private theorem apply_heq {C : Type} {m₁ m₂ : ℕ} (h : m₁ = m₂) {A₁ : (Fin m₁ → Digest) → C}
    {A₂ : (Fin m₂ → Digest) → C} (hA : HEq A₁ A₂) (ds : Fin m₂ → Digest) :
    A₁ (fun j ↦ ds (Fin.cast h j)) = A₂ ds := by
  subst h
  cases hA
  rfl

/-- The prefix of a transcript before a challenge, with its length. -/
private def _root_.LeanerVM.Protocol.SlotReader.prefixOf (R : SlotReader) {a : R.Ann}
    (tr : (R.spec a).FullTranscript) (i : (R.spec a).ChallengeIdx) :
    Σ k : Fin (R.n a + 1), (R.spec a).Transcript k :=
  ⟨i.1.castSucc, prefixBefore tr i⟩

/-- **A bad challenge of a decoded history flips its group**, for any reader whose prefixes are
those of a decoder whose challenges read squeezes alone: on a log with no collision holding the
history's steps from a start that opens a statement, its later states no starts, the group of a
challenge of the decoded transcript that is bad at the prefix before it is closed on it, its proof
of work passing. -/
private theorem _root_.LeanerVM.Protocol.SlotReader.flipAt_of_decoder (R : SlotReader)
    {l : hashSpec.QueryLog} (hc : QueryLog.Consistent l) (hcoll : ¬ QueryLog.HasCollision l)
    {σ : Digest} {st : R.Stmt} (hσ : R.stmtAt l σ = some st) {a : R.Ann} {hist : List Reading}
    (hstates : ∀ x ∈ hist.map (·.2), R.isStart l x = false)
    (hchain : ∀ e ∈ HashChain.queries Block.input σ hist, e ∈ l)
    (hobs : ∀ j < 10, ∃ x d, hist[j]? = some (.observe x, d))
    (hann : ∀ hs : List Reading, 8 ≤ hs.length → hs <+: hist → R.announcementOf st hs = some a)
    (hpow : ∀ (j : ℕ) n d, hist[j]? = some (.nonce n, d) →
      PowPasses R.powBits l (HashChain.last σ (hist.take j)) n)
    (hnonce : ∀ (hs : List Reading) n d, R.wordsAt a l (hs ++ [(.nonce n, d)]) = R.wordsAt a l hs)
    (D : R.Words a → SlotDecoder Reading (R.spec a)) (f : ChalSlots (R.spec a))
    (hD : ∀ W hs, R.decodePrefix a W hs = (D W).decodePrefix hs)
    (hS : ∀ W, SqueezeReads (D W) f) (hO : ∀ W, SqueezesOnly (D W)) (hP : f.Pos)
    (hm : ∀ i, (R.slot a i).m = (f i.1 i.2).m)
    (hasm : ∀ i, HEq (R.slot a i).assemble (f i.1 i.2).assemble)
    {W : R.Words a}
    (hwords : ∀ c rest, hist = c ++ rest →
      (D (R.wordsAt a l c)).decodePrefix c = (D W).decodePrefix c)
    {tr : (R.spec a).FullTranscript} (hdec : (D W).decode hist = some tr)
    (i : (R.spec a).ChallengeIdx) (hbad : R.BadIn tr i) : R.FlipAt l := by
  have hcut := challenge_cut (hS W) (hO W) hP hdec i
  obtain ⟨c, hcut⟩ := hcut
  obtain ⟨ds₀, hcut⟩ := hcut
  obtain ⟨rest, hl₀, hpre₀, hchal₀⟩ := hcut
  have hpre : R.decodePrefix a (R.wordsAt a l c) c = some (R.prefixOf tr i) :=
    ((hD _ _).trans (hwords c _ hl₀)).trans hpre₀
  set ds : Fin (R.slot a i).m → Digest := fun j ↦ ds₀ (Fin.cast (hm i) j) with hds_def
  have hds : List.ofFn ds = List.ofFn ds₀ := by
    refine List.ext_getElem (by simp [hm i]) fun k h₁ h₂ ↦ ?_
    simp [hds_def]
  have hchal : tr i.1 = (R.slot a i).assemble ds := by
    rw [hchal₀]
    exact (apply_heq (hm i) (hasm i) ds₀).symm
  have hl : hist = c ++ (squeezeBlocks (List.ofFn ds) ++ rest) := by rw [hds]; exact hl₀
  have hpos : 0 < (R.slot a i).m := R.slot_pos a i
  have hstart : R.isStart l σ = true := by simp [ChainStarts.isStart, hσ]
  -- the history's first readings are observes
  have h10 : ∀ (j : ℕ) (b : Block) (d : Digest), hist[j]? = some (b, d) → (∀ x, b ≠ .observe x) →
      10 ≤ j := by
    intro j b d h hb
    by_contra hlt
    obtain ⟨x, d', hx⟩ := hobs j (by omega)
    rw [h, Option.some.injEq, Prod.mk.injEq] at hx
    exact hb x hx.1
  have hc10 : 10 ≤ c.length :=
    h10 c.length .squeeze (ds ⟨0, hpos⟩) (by rw [hl]; exact getElem?_cut hpos ds)
      (fun x h ↦ nomatch h)
  -- the squeezes' queries and their run
  have hqs : ∀ e ∈ HashChain.queries Block.input (HashChain.last σ c)
      (squeezeBlocks (List.ofFn ds)), e ∈ l := by
    intro e he
    refine hchain e ?_
    rw [hl, HashChain.queries_append, HashChain.queries_append]
    exact List.mem_append_right _ (List.mem_append_left _ he)
  have hrun : squeezeRun l (HashChain.last σ c) (R.slot a i).m = List.ofFn ds := by
    have := squeezeRun_of_chain hc _ _ hqs
    rwa [List.length_ofFn] at this
  have hgetD : (fun j : Fin (R.slot a i).m ↦ (List.ofFn ds).getD j default) = ds := by
    funext j
    simp
  have hasc : asChallenge (R.prefixOf tr i) = some ⟨i, prefixBefore tr i⟩ := by
    simp [asChallenge, SlotReader.prefixOf, i.2]
  have hbad' : (R.slot a i).assemble ds ∈ R.Bad a i (prefixBefore tr i) := by
    rw [← hchal]
    exact hbad
  by_cases hmk : R.mark a i = true
  · -- a marked challenge: the group of its nonce
    obtain ⟨hs₀, n, d, rfl⟩ := R.mark_afterNonce a _ c i _ hpre hmk
    have hhist : hist = hs₀ ++ ((.nonce n, d) :: (squeezeBlocks (List.ofFn ds) ++ rest)) := by
      rw [hl]
      simp
    have hnth : hist[hs₀.length]? = some (.nonce n, d) := by
      rw [hhist]
      simp
    have h10' : 10 ≤ hs₀.length := h10 _ _ _ hnth (fun x h ↦ nomatch h)
    have htake : hist.take hs₀.length = hs₀ := by
      rw [hhist]
      simp
    have hch : chainHistory l (R.isStart l) ⟨HashChain.last σ hs₀⟩ = some (σ, hs₀) := by
      have := LeanVmReader.chainHistory_of_log hcoll hstart hstates hchain hs₀.length
      rwa [htake] at this
    have hdp : R.decodePrefix a (R.wordsAt a l hs₀) (hs₀ ++ [(.nonce n, default)]) =
        some (R.prefixOf tr i) := by
      rw [R.decodePrefix_digest_indep a _ hs₀ (.nonce n) default d [] (fun h ↦ nomatch h),
        ← hnonce hs₀ n d]
      exact hpre
    have hgs : R.groupSlot l ⟨HashChain.last σ hs₀, some n⟩ =
        some ⟨a, i, prefixBefore tr i⟩ := by
      simp only [SlotReader.groupSlot, Group.nonceBlock, Option.toList_some, List.map_cons,
        List.map_nil]
      simp only [hch, Option.bind_eq_bind, Option.bind_some, hσ, hann hs₀ (by omega)
        ⟨_, hhist.symm⟩, hdp, hasc]
      simp [hmk]
    have hstart : MerkleTree.logAnswer l (absorbInput (HashChain.last σ hs₀) n) = some d :=
      logAnswer_of_consistent hc (e := ⟨Block.input (HashChain.last σ hs₀) (.nonce n), d⟩)
        (hchain _ (by
          rw [hhist, HashChain.queries_append]
          simp [HashChain.queries]))
    have hlast : HashChain.last σ (hs₀ ++ [(.nonce n, d)]) = d := by
      rw [HashChain.last_append]
      rfl
    refine ⟨⟨HashChain.last σ hs₀, some n⟩, ?_⟩
    unfold SlotReader.Flips
    rw [hgs]
    have hgrun : Group.run l ⟨HashChain.last σ hs₀, some n⟩ (R.slot a i).m = List.ofFn ds := by
      rw [← hrun, hlast]
      simp only [Group.run, Group.start?, hstart]
    refine ⟨?_, ?_, ?_⟩
    · rw [hgrun, List.length_ofFn]
    · rintro n' hn'
      cases hn'
      have := hpow hs₀.length n d hnth
      rwa [htake] at this
    · rw [hgrun, hgetD]
      exact hbad'
  · -- a plain challenge: the group of its state
    have hmk' : R.mark a i = false := Bool.eq_false_iff.mpr hmk
    have htake : hist.take c.length = c := by
      rw [hl]
      simp
    have hch : chainHistory l (R.isStart l) ⟨HashChain.last σ c⟩ = some (σ, c) := by
      have := LeanVmReader.chainHistory_of_log hcoll hstart hstates hchain c.length
      rwa [htake] at this
    have hgs : R.groupSlot l ⟨HashChain.last σ c, none⟩ =
        some ⟨a, i, prefixBefore tr i⟩ := by
      simp only [SlotReader.groupSlot, Group.nonceBlock, Option.toList_none, List.map_nil,
        List.append_nil]
      simp only [hch, Option.bind_eq_bind, Option.bind_some, hσ, hann c (by omega)
        ⟨_, hl.symm⟩, hpre, hasc]
      simp [hmk']
    refine ⟨⟨HashChain.last σ c, none⟩, ?_⟩
    unfold SlotReader.Flips
    rw [hgs]
    have hgrun : Group.run l ⟨HashChain.last σ c, none⟩ (R.slot a i).m = List.ofFn ds := by
      rw [← hrun]
      rfl
    refine ⟨?_, (fun _ h ↦ nomatch h), ?_⟩
    · rw [hgrun, List.length_ofFn]
    · rw [hgrun, hgetD]
      exact hbad'

open LeanVmReader in
/-- **A bad challenge of the verifier's history flips its group**: on a log holding the history's
steps, with no collision and no answer equal to the seed, the group of a challenge of the decoded
transcript that is bad at the prefix before it is closed on it, its proof of work passing. -/
theorem flipAt_of_bad {prog : Program} {input : PublicInput} {l : hashSpec.QueryLog}
    (hc : QueryLog.Consistent l) (hcoll : ¬ QueryLog.HasCollision l)
    (hseed : ∀ e ∈ l, e.2 ≠ (FsState.seed prog input).cv) {a : Ann prog} {hist : List Reading}
    (hchain : ∀ e ∈ HashChain.queries Block.input (FsState.seed prog input).cv hist, e ∈ l)
    (hobs : ∀ j < 10, ∃ x d, hist[j]? = some (.observe x, d))
    (hann : announcementOf prog hist = some a)
    (hpow : ∀ (j : ℕ) n d, hist[j]? = some (.nonce n, d) →
      PowPasses LeanerVM.Parameters.Whir.queryGrindingBits l
        (HashChain.last (FsState.seed prog input).cv (hist.take j)) n)
    {W : LeanWords prog a.1.1 a.2.1 a.1.2 a.2.2}
    (hW : W = wordsOf prog input a.1.1 a.2.1 a.1.2 a.2.2 l hist)
    {tr : (deployedSpec Blake2sFlock.blake2sFlockSpec prog a.1.1 a.2.1 a.1.2 a.2.2).FullTranscript}
    (hdec : (decoder prog input a.1.1 a.2.1 a.1.2 a.2.2 W).decode hist = some tr)
    (i : (deployedSpec Blake2sFlock.blake2sFlockSpec prog a.1.1 a.2.1 a.1.2 a.2.2).ChallengeIdx)
    (hbad : challengeAt tr i ∈ Bad Blake2sFlock.blake2sFlockSpec prog a.1.1 a.2.1 a.1.2 a.2.2
      (input, fun j ↦ j.elim0) i (prefixBefore tr i)) :
    (leanVmReader prog input).FlipAt l := by
  have hstates : ∀ x ∈ hist.map (·.2),
      (leanVmReader prog input).isStart l x = false := fun x hx ↦ by
    obtain ⟨e, he, rfl⟩ := HashChain.answer_of_mem_states hchain hx
    show (ChainStarts.startAt (FsState.seed prog input).cv).isStart l e.2 = false
    simpa [HashChain.isSeed] using hseed e he
  dsimp only [leanVmReader]
  refine SlotReader.flipAt_of_decoder _ (a := a) hc hcoll (σ := (FsState.seed prog input).cv)
    (st := ()) (ChainStarts.stmtAt_startAt _ l) hstates hchain hobs
    (fun hs h8 hpfx ↦ ?_) hpow (fun hs n d ↦ wordsOf_append_nonce prog input _ _ _ _ l hs n d)
    (fun W ↦ decoder prog input a.1.1 a.2.1 a.1.2 a.2.2 W) (famAt a) (fun _ _ ↦ rfl)
    (fun W ↦ (readsWell_decoder prog input a W).squeezes)
    (fun W ↦ squeezesOnly_compiledDec (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog a.1.1)
      (leanIsa_conditions _ prog a.1.1) input (announcement a.1.1 a.1.2)
      (leanIsaChain prog a.1.1 a.2.1 a.1.2 a.2.2) W)
    (pos_compiledFam (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog a.1.1)
      (leanIsaChain prog a.1.1 a.2.1 a.1.2 a.2.2) (posOk_leanIsaChain a.2.1 a.2.2))
    (fun _ ↦ by dsimp only [UniformSlot.slotAt]) (fun _ ↦ by dsimp only [UniformSlot.slotAt]; rfl)
    (W := W) (tr := tr) (fun c rest h ↦ ?_) (by dsimp only; exact hdec) i
    (by dsimp only [SlotReader.BadIn]; exact hbad)
  · show announcementOf prog hs = some a
    rw [← hann]
    unfold announcementOf
    obtain ⟨r, rfl⟩ := hpfx
    rw [List.take_append_of_le_length h8]
  · have h' := DecodeAgree.decodePrefix_words_congr (prog := prog) (input := input) (s := a.1.1)
      (hs := a.2.1) (ρ := a.1.2) (hρ := a.2.2) (W := wordsOf prog input a.1.1 a.2.1 a.1.2 a.2.2 l c)
      (W' := W) (hist := c) (by rw [hW, h]; exact wordsOf_prefix prog input _ _ _ _ l c _)
    unfold DecodeChain.decodePrefix at h'
    exact h'

end Core

end

end LeanerVM.Protocol
