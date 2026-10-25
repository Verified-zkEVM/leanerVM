/-
  LeanerVM.Protocol.Core.History

  What the verifier's chain history says about the proof: its first readings are the announced
  sizes and the commitment's root, and the levels it walks carry their roots.
-/

module

public import LeanerVM.Protocol.Core.Decoded
public import LeanerVM.Protocol.Core.Openings

/-!
# The verifier's chain history

The chain walk the verifier logs reads its history off the proof's stream. The setup reads ten
observes first, the eight announced sizes and the commitment's root (`observes_of_walkChain`),
so the history's announcement is the proof's (`announcementOf_of_setup`) and its level-0 root
is the proof's (`rootAt_eq_level0Root`). Every level of WHIR's opening with a successor reads a
root (`RootsShaped`, `rootsShaped_of_walkChain`), so when the decoded transcript carries the
words read off a log under the roots the history carries, each later word is the one read under
its level's root (`ladderRoots_of`). With no hit on the seed, no answer of the log is the seed
(`seed_not_answer`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa ProtocolSpec StepSchedule Verify
open DecodeChain Whir SlotDecoder ProofRoots OracleSpec

@[expose] public section

namespace Core

/-! ## The seed and the setup -/


/-- With no hit on the seed, no answer of a consistent log is the seed. -/
theorem seed_not_answer {prog : Program} {input : PublicInput} {l : hashSpec.QueryLog}
    (hc : QueryLog.Consistent l)
    (hhit : ¬ QueryLog.HasHit (inPlay (seedDigests prog input)) l) :
    ∀ e ∈ l, e.2 ≠ (FsState.seed prog input).cv := fun e he h ↦
  QueryLog.answer_not_mem_inPlay_nil (inPlay_mono _) hc hhit he (by simp [inPlay, seedDigests, h])

/-- `k` scalars read off a history are `k` observes. -/
private theorem observes_of_nextScalars : ∀ (k : ℕ) {l : List Reading} {x : List E}
    {r : List Reading},
    (historyOps.nextScalars k).read l = some (x, r) →
    ∃ c, l = c ++ r ∧ c.length = k ∧ ∀ e ∈ c, ∃ y d, e = (.observe y, d)
  | 0, l, x, r, h => by
    simp only [ChainOps.nextScalars, Slot.read_pure, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], by simp [h.2], rfl, by simp⟩
  | k + 1, l, x, r, h => by
    simp only [ChainOps.nextScalars, Slot.read_bind, Option.bind_eq_some_iff, Slot.read_pure,
      Option.some.injEq, Prod.mk.injEq, Prod.exists] at h
    obtain ⟨y, l₁, h₁, ys, l₂, h₂, -, rfl⟩ := h
    rcases l with _ | ⟨⟨b, d⟩, l⟩
    · exact nomatch h₁
    change (scalarOf (b, d)).map (·, l) = some (y, l₁) at h₁
    cases b with
    | observe z =>
      simp only [scalarOf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h₁
      obtain ⟨-, hl⟩ := h₁
      subst hl
      obtain ⟨c, hc', hc, hobs⟩ := observes_of_nextScalars k h₂
      refine ⟨(.observe z, d) :: c, by rw [hc']; rfl, by simp [hc], fun e he ↦ ?_⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨z, d, rfl⟩
      · exact hobs e he
    | squeeze => simp [scalarOf] at h₁
    | nonce _ => simp [scalarOf] at h₁

private theorem observe_of_next {l : List Reading} {x : E} {r : List Reading}
    (h : (Slot.next scalarOf).read l = some (x, r)) : ∃ d, l = (.observe x, d) :: r := by
  rcases l with _ | ⟨⟨b, d⟩, l⟩
  · exact nomatch h
  change (scalarOf (b, d)).map (·, l) = some (x, r) at h
  cases b with
  | observe z =>
    simp only [scalarOf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨d, rfl⟩
  | squeeze => simp [scalarOf] at h
  | nonce _ => simp [scalarOf] at h

/-- **The setup on a history reads ten observes**: the announced sizes and the commitment's
root. -/
private theorem observes_of_walkSetup {l : List Reading} {d : Digest} {r : List Reading}
    (h : (walkSetup historyOps).read l = some (d, r)) :
    ∃ c, l = c ++ r ∧ c.length = 10 ∧ ∀ e ∈ c, ∃ y d, e = (.observe y, d) := by
  simp only [walkSetup, Slot.read_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨xs, l₁⟩, h₁, h₂⟩ := h
  obtain ⟨c₁, rfl, hc₁, ho₁⟩ := observes_of_nextScalars 8 h₁
  simp only [historyOps, Slot.read_bind, Option.bind_eq_some_iff] at h₂
  obtain ⟨⟨a, l₂⟩, ha, ⟨b, l₃⟩, hb, hm⟩ := h₂
  obtain ⟨da, rfl⟩ := observe_of_next ha
  obtain ⟨db, rfl⟩ := observe_of_next hb
  have hr : l₃ = r := by
    split at hm
    · simp only [Slot.read_pure, Option.some.injEq, Prod.mk.injEq] at hm
      exact hm.2
    · exact nomatch hm
  subst hr
  refine ⟨c₁ ++ [(.observe a, da), (.observe b, db)], by simp, by simp [hc₁], fun e he ↦ ?_⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | rfl | rfl
  · exact ho₁ e he
  · exact ⟨a, da, rfl⟩
  · exact ⟨b, db, rfl⟩

/-- **The chain walk on a history reads ten observes first**: the announced sizes and the
commitment's root. -/
theorem observes_of_walkChain {prog : Program} {s : Sizes} {input : PublicInput}
    {shs : List LevelShape} {hist : List Reading} {w : Wire} {r : List Reading}
    (h : (walkChain historyOps prog s input shs).read hist = some (w, r)) :
    ∀ j < 10, ∃ x d, hist[j]? = some (.observe x, d) := by
  rw [walkChain_eq_setup, Slot.read_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨root, l₁⟩, h₁, -⟩ := h
  obtain ⟨c, rfl, hc, hobs⟩ := observes_of_walkSetup h₁
  intro j hj
  obtain ⟨y, d, hyd⟩ := hobs (c[j]'(by omega)) (List.getElem_mem _)
  exact ⟨y, d, by rw [List.getElem?_append_left (by omega), List.getElem?_eq_getElem
    (by omega), hyd]⟩



/-! ## The history's leading observes are the proof's stream -/

/-- The scalars of a history's leading observes are its stream's. -/
private theorem getElem?_streamOf : ∀ (j : ℕ) (hist : List Reading),
    (∀ k ≤ j, ∃ x d, hist[k]? = some (.observe x, d)) →
    ∀ x d, hist[j]? = some (.observe x, d) → (streamOf hist)[j]? = some x
  | _, [], _, _, _, h => nomatch h
  | 0, (b, d') :: rest, _, x, d, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | j + 1, (b, d') :: rest, hobs, x, d, h => by
    obtain ⟨y, d₀, h₀⟩ := hobs 0 (Nat.zero_le _)
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h₀
    obtain ⟨rfl, rfl⟩ := h₀
    rw [List.getElem?_cons_succ] at h
    rw [show streamOf ((Block.observe y, d') :: rest) = y :: streamOf rest from rfl,
      List.getElem?_cons_succ]
    exact getElem?_streamOf j rest
      (fun k hk ↦ by simpa using hobs (k + 1) (by omega)) x d h

private theorem streamOf_take {hist : List Reading} {k : ℕ}
    (hobs : ∀ j < k, ∃ x d, hist[j]? = some (.observe x, d)) :
    streamOf (hist.take k) = (streamOf hist).take k := by
  refine List.ext_getElem? fun n ↦ ?_
  rcases Nat.lt_or_ge n k with hn | hn
  · obtain ⟨x, d, h⟩ := hobs n hn
    have hobs' : ∀ m ≤ n, ∃ x d, (hist.take k)[m]? = some (.observe x, d) := fun m hm ↦ by
      rw [List.getElem?_take, ite_eq_left (by omega)]
      exact hobs m (by omega)
    rw [getElem?_streamOf n _ hobs' x d (by rw [List.getElem?_take, ite_eq_left hn]; exact h),
      List.getElem?_take, ite_eq_left hn,
      getElem?_streamOf n hist (fun m hm ↦ hobs m (by omega)) x d h]
  · rw [List.getElem?_take, ite_eq_right (by omega), List.getElem?_eq_none]
    exact (List.length_filterMap_le _ _).trans ((List.length_take_le _ _).trans hn)

private theorem ten_le_length {hist : List Reading}
    (hobs : ∀ j < 10, ∃ x d, hist[j]? = some (.observe x, d)) : 10 ≤ (streamOf hist).length := by
  obtain ⟨x, d, h⟩ := hobs 9 (by omega)
  exact (List.getElem?_eq_some_iff.mp
    (getElem?_streamOf 9 hist (fun k hk ↦ hobs k (by omega)) x d h)).1

/-- **The announcement of the verifier's history** is the proof's, at the sizes and rate the
setup accepts. -/
theorem announcementOf_of_setup {prog : Program} {proof : Proof PrunedMerklePaths} {s : Sizes}
    {ρ : ℕ} (hsetup : setup? prog proof = some (s, ρ)) (hs : s.Admissible prog)
    (hρ : validRate ρ) {hist : List Reading} {rest : List E}
    (hst : proof.stream = streamOf hist ++ rest)
    (hobs : ∀ j < 10, ∃ x d, hist[j]? = some (.observe x, d)) :
    LeanVmReader.announcementOf prog hist = some ⟨(s, ρ), hs, hρ⟩ := by
  have h8 : streamOf (hist.take 8) = proof.stream.take 8 := by
    rw [streamOf_take fun j hj ↦ hobs j (by omega), hst,
      List.take_append_of_le_length (by have := ten_le_length hobs; omega)]
  have ha := LeanVmReader.announced?_of_setup hsetup
  rw [show proof.announced? = decodeAnnouncement (proof.stream.take 8) from rfl] at ha
  unfold LeanVmReader.announcementOf
  rw [h8, ha, Option.bind_some, dite_eq_left ⟨hs, hρ⟩]

/-- **The level-0 root of the verifier's history** is the proof's. -/
theorem rootAt_eq_level0Root {proof : Proof PrunedMerklePaths} {hist : List Reading}
    {rest : List E} (hst : proof.stream = streamOf hist ++ rest)
    (hobs : ∀ j < 10, ∃ x d, hist[j]? = some (.observe x, d)) :
    rootAt hist 8 = level0Root proof := by
  obtain ⟨x₈, d₈, h₈⟩ := hobs 8 (by omega)
  obtain ⟨x₉, d₉, h₉⟩ := hobs 9 (by omega)
  have s₈ := getElem?_streamOf 8 hist (fun k hk ↦ hobs k (by omega)) x₈ d₈ h₈
  have s₉ := getElem?_streamOf 9 hist (fun k hk ↦ hobs k (by omega)) x₉ d₉ h₉
  have p₈ : proof.stream[8]? = some x₈ := by
    rw [hst, List.getElem?_append_left (List.getElem?_eq_some_iff.mp s₈).1, s₈]
  have p₉ : proof.stream[9]? = some x₉ := by
    rw [hst, List.getElem?_append_left (List.getElem?_eq_some_iff.mp s₉).1, s₉]
  unfold rootAt level0Root
  rw [h₈, h₉]
  have q₀ : (proof.stream.drop 8)[0]? = some x₈ := by rw [List.getElem?_drop]; exact p₈
  have q₁ : (proof.stream.drop 8)[1]? = some x₉ := by rw [List.getElem?_drop]; exact p₉
  rcases hd : proof.stream.drop 8 with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> rw [hd] at q₀ q₁
  · cases q₀
  · cases q₁
  · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at q₀ q₁
    subst q₀ q₁
    rfl


/-! ## The walk's levels carry their roots -/

/-- The levels carry a root exactly where the shapes have a successor. -/
def RootsShaped : List LevelShape → List WhirLevel → Prop
  | [], [] => True
  | sh :: shs, lv :: ls => (sh.final = false → lv.root.isSome) ∧ RootsShaped shs ls
  | _, _ => False

private theorem always_walkLevel_root (sh : LevelShape) :
    Always (walkLevel historyOps sh) fun lv ↦ sh.final = false → lv.root.isSome := by
  cases hf : sh.final
  · simp only [walkLevel, hf, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_map_left]
    repeat' refine Always.bind (Always.true _) fun _ _ ↦ ?_
    exact Always.pure fun _ ↦ rfl
  · exact (Always.true _).mono fun _ _ h ↦ nomatch h

private theorem always_walkLevels :
    ∀ shs : List LevelShape, Always (walkLevels historyOps shs) (RootsShaped shs)
  | [] => by
    simp only [walkLevels]
    exact Always.pure trivial
  | sh :: shs => by
    simp only [walkLevels]
    exact Always.bind (always_walkLevel_root sh) fun lv hlv ↦
      Always.bind (always_walkLevels shs) fun ls hls ↦ Always.pure ⟨hlv, hls⟩

/-- **The walk's levels carry their roots**: on a history the chain walk reads, every level with
a successor carries a root. -/
theorem rootsShaped_of_walkChain {prog : Program} {s : Sizes} {input : PublicInput}
    {shs : List LevelShape} {hist : List Reading} {w : Wire} {r : List Reading}
    (h : (walkChain historyOps prog s input shs).read hist = some (w, r)) :
    RootsShaped shs w.whir := by
  have hW : Always (walkWhir historyOps shs) fun p ↦ RootsShaped shs p.2 := by
    simp only [walkWhir]
    exact Always.bind (Always.true _) fun _ _ ↦
      Always.bind (always_walkLevels shs) fun _ hls ↦ Always.pure hls
  have key : Always (walkChain historyOps prog s input shs) fun w ↦ RootsShaped shs w.whir := by
    simp only [walkChain]
    refine Always.bind (Always.true _) fun _ _ ↦ Always.bind (Always.true _) fun _ _ ↦
      Always.bind (Always.true _) fun _ _ ↦ Always.bind (Always.true _) fun _ _ ↦
      Always.bind (Always.true _) fun _ _ ↦ Always.bind (Always.true _) fun _ _ ↦
      Always.bind hW fun p hp ↦ ?_
    obtain ⟨first, whir⟩ := p
    exact Always.pure hp
  exact key _ _ _ h


/-- **Each later word is read off the log under its level's root**, when the transcript carries
the words read under the roots the levels carry. -/
theorem ladderRoots_of {l : hashSpec.QueryLog} : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (t : (seqSpec L.steps).FullTranscript) (ls : List WhirLevel),
    LadderWords L (LeanVmReader.laterWords l L ((ls.filterMap (·.root)).map some)) t →
    RootsShaped L.shapes ls → LadderRoots l L t ls
  | _, _, .last _ _, _, _, _, _ => trivial
  | _, _, @Ladder.cons _ sh' κ' L, t, [], _, hr => by
    simp [Whir.Ladder.shapes, RootsShaped] at hr
  | _, _, @Ladder.cons _ sh' κ' L, t, lv :: ls, hw, hr => by
    simp only [Whir.Ladder.shapes, RootsShaped] at hr
    have h₁ : lv.root.isSome := by simpa using hr.1
    obtain ⟨root, hroot⟩ := Option.isSome_iff_exists.mp h₁
    simp only [List.filterMap_cons, hroot, List.map_cons, LeanVmReader.laterWords, LadderWords,
      List.headD_cons, List.tail_cons] at hw
    exact ⟨⟨root, hroot, hw.1⟩, ladderRoots_of L _ ls hw.2 hr.2⟩

end Core

end

end LeanerVM.Protocol
