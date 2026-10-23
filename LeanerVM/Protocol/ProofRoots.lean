/-
  LeanerVM.Protocol.ProofRoots

  The roots a proof's stream carries where the verifier's chain walk reads them: at offsets of the
  stream fixed by the sizes, at most six, and the roots the walk reads on its history are those.
-/

module

public import LeanerVM.Protocol.Verify.Count
public import LeanerVM.Protocol.DecodeWire

/-!
# The proof's roots

The chain walk reads a root as two scalars of the stream, at an offset that depends on the sizes
alone: no walk's consumption of the stream depends on a value it reads (`walkChain_grade` at
`scalarCounts`: a scalar one, a challenge none, a root two, a nonce one). The level-0 root is at
offset `8`, after the announced sizes; each later level's root after the scalars of the levels
before it and of its own fold rounds (`rootOffsets`). `rootsOf prog input proof` is the digests the
proof's stream carries at those offsets, at the sizes and rate it announces; there are at most
`proofDigests = 6` (`length_rootsOf_le`), the deployed ladders having at most five levels.

`walkChain_roots`: the roots the chain walk reads on a history are the digests of the history's
stream at the offsets, all present; `rootsOf_eq_of_walkChainLogged`: the roots the verifier's
chain walk reads on a proof, its steps logged, are `rootsOf prog input proof`, in order.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa Verify DecodeChain

@[expose] public section

namespace ProofRoots

/-- The stream's scalars each primitive reads: a scalar one, a challenge none, a root two, a
nonce one. -/
def scalarCounts : StepCounts := ⟨1, 0, 2, fun _ ↦ 1⟩

/-- The offsets of the roots the levels `shs` read, the first level starting at offset `o`: one
per level with a successor, after its fold rounds. -/
def levelRootOffsets : ℕ → List LevelShape → List ℕ
  | _, [] => []
  | o, sh :: shs => (if sh.final then [] else [o + scalarCounts.folds sh.fold]) ++
      levelRootOffsets (o + scalarCounts.level sh) shs

/-- The offset at which WHIR's levels start: after the setup, the four front phases and the first
round polynomial. -/
def whirStart (prog : Program) (s : Sizes) (input : PublicInput) : ℕ :=
  scalarCounts.setup + scalarCounts.bus (leanVm prog s).μBus (leanVm prog s).busClaims +
    scalarCounts.tables (leanVm prog s).τmax (leanVm prog s).tableColumns +
    scalarCounts.pub (PublicInput.sentCount (leanVm prog s) ((leanVm prog s).publicLines input)) +
    scalarCounts.flock (s.τ 5) + scalarCounts.sample + 2 * scalarCounts.scalar

/-- The offsets of the roots the chain walk reads: the level-0 root after the eight announced
sizes, then the later levels' roots. -/
def rootOffsets (prog : Program) (s : Sizes) (input : PublicInput) (shs : List LevelShape) :
    List ℕ :=
  8 :: levelRootOffsets (whirStart prog s input) shs

/-- The digest a stream carries at an offset: its two scalars there, when canonical. -/
def digestAt (stream : List E) (o : ℕ) : Option Digest :=
  match stream.drop o with
  | x₁ :: x₂ :: _ => digestOfScalars (x₁, x₂)
  | _ => none

/-- **The proof's roots**: the digests its stream carries where the verifier's chain walk reads
its roots, at the sizes and rate it announces; none when the setup rejects it. -/
def rootsOf (prog : Program) (input : PublicInput) (proof : Proof PrunedMerklePaths) :
    List Digest :=
  match setup? prog proof with
  | none => []
  | some (s, ρ) =>
    match ladderOf prog s ρ with
    | none => []
    | some levels =>
      (rootOffsets prog s input (levelShapes (stackMu prog s) levels)).filterMap
        (digestAt proof.stream)

/-- The most roots a proof has. -/
def proofDigests : ℕ := 6

/-- One root per level with a successor. -/
theorem length_levelRootOffsets : ∀ (o : ℕ) (shs : List LevelShape),
    (levelRootOffsets o shs).length = (shs.filter fun sh ↦ !sh.final).length
  | _, [] => rfl
  | o, sh :: shs => by
    rw [levelRootOffsets, List.length_append, length_levelRootOffsets, List.filter_cons]
    cases sh.final <;> simp [Nat.add_comm]

/-- A ladder's levels all have a successor but the last. -/
theorem length_filter_levelShapes : ∀ (μ : ℕ) (levels : List Whir.Level),
    ((levelShapes μ levels).filter fun sh ↦ !sh.final).length = levels.length - 1
  | _, [] => rfl
  | _, [_] => rfl
  | μ, l :: l' :: ls => by
    have ih := length_filter_levelShapes (μ - l.fold) (l' :: ls)
    simp only [levelShapes, List.filter_cons, Bool.not_false, ↓reduceIte, List.length_cons, ih]
    simp

/-- The deployed ladders have at most six levels. -/
theorem length_ladder_le {μ ρ : ℕ} {levels : List Whir.Level}
    (h : Whir.ladder μ ρ = some levels) : levels.length ≤ 6 := by
  have hadm : Whir.Admissible μ ρ := by
    unfold Whir.ladder at h
    split_ifs at h with h'
    exact h'
  have key : ∀ μ < Whir.maxLogStack + 1, ∀ ρ < Whir.maxLogInvRate + 1,
      ∀ ls ∈ Whir.ladder μ ρ, ls.length ≤ 6 := by
    decide +kernel
  exact key μ (Nat.lt_succ_of_le hadm.2.1) ρ (Nat.lt_succ_of_le hadm.2.2.2) levels h

/-- **A proof has at most six roots.** -/
theorem length_rootsOf_le (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) : (rootsOf prog input proof).length ≤ proofDigests := by
  unfold rootsOf
  rcases setup? prog proof with _ | ⟨s, ρ⟩
  · exact Nat.zero_le _
  · dsimp only
    rcases hl : ladderOf prog s ρ with _ | levels
    · exact Nat.zero_le _
    · dsimp only
      refine (List.length_filterMap_le _ _).trans ?_
      have := length_ladder_le hl
      simp only [rootOffsets, List.length_cons, length_levelRootOffsets,
        length_filter_levelShapes, proofDigests]
      omega


/-! ## The roots the walk reads -/

section Walk

open Slot

/-- The slots that read exactly `n` of the stream's scalars wherever they read. -/
def streamGrade : MonadGrade (Slot Reading) where
  P a n := ∀ l x r, a.read l = some (x, r) → ∃ c, l = c ++ r ∧ (streamOf c).length = n
  pure x l y r h := by
    rw [read_pure, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], by simp [h.2], rfl⟩
  bind {α β a f n k} ha hf l x r h := by
    rw [read_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨y, l₁⟩, h₁, h₂⟩ := h
    obtain ⟨c₁, rfl, hc₁⟩ := ha _ _ _ h₁
    obtain ⟨c₂, rfl, hc₂⟩ := hf y _ _ _ h₂
    exact ⟨c₁ ++ c₂, by simp, by rw [streamOf_append, List.length_append, hc₁, hc₂]⟩

theorem next_grade {β : Type} {f : Reading → Option β} {k : ℕ}
    (hf : ∀ a y, f a = some y → (streamOf [a]).length = k) : streamGrade.P (Slot.next f) k := by
  rintro (_ | ⟨a, l⟩) x r h
  · exact nomatch h
  · rw [read_next_cons, Option.map_eq_some_iff] at h
    obtain ⟨y, hy, he⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨[a], rfl, hf a y hy⟩

theorem fail_grade {β : Type} (n : ℕ) : streamGrade.P (Slot.fail : Slot Reading β) n :=
  fun _ _ _ h ↦ nomatch h

/-- **The history reader's primitives, counted** in the stream's scalars they read. -/
theorem historyOps_graded : ChainOps.Graded streamGrade historyOps scalarCounts where
  nextScalar := next_grade (k := 1) fun ⟨b, _⟩ y h ↦ by cases b <;> simp_all [scalarOf, streamOf]
  sample := next_grade (k := 0) fun ⟨b, _⟩ y h ↦ by cases b <;> simp_all [challengeOf, streamOf]
  nextRoot := streamGrade.of_eq (streamGrade.bind
    (next_grade (k := 1) fun ⟨b, _⟩ y h ↦ by cases b <;> simp_all [scalarOf, streamOf]) fun _ ↦
    streamGrade.bind (k := 0)
      (next_grade (k := 1) fun ⟨b, _⟩ y h ↦ by cases b <;> simp_all [scalarOf, streamOf])
      fun _ ↦ by
    split
    · exact streamGrade.pure _
    · exact fail_grade _) rfl
  checkPow _ := next_grade (k := 1) fun ⟨b, _⟩ y h ↦ by cases b <;> simp_all [nonceOf, streamOf]

/-- A graded slot reads a prefix of exactly its count of scalars. -/
theorem read_bind_of_grade {α β : Type} {a : Slot Reading α} {f : α → Slot Reading β} {n : ℕ}
    (ha : streamGrade.P a n) {l : List Reading} {x : β} {r : List Reading}
    (h : (a >>= f).read l = some (x, r)) :
    ∃ y l₁, a.read l = some (y, l₁) ∧ (f y).read l₁ = some (x, r) ∧
      ∃ s, streamOf l = s ++ streamOf l₁ ∧ s.length = n := by
  rw [read_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨y, l₁⟩, h₁, h₂⟩ := h
  obtain ⟨c, rfl, hc⟩ := ha _ _ _ h₁
  exact ⟨y, l₁, h₁, h₂, streamOf c, streamOf_append _ _, hc⟩

theorem digestAt_append (s t : List E) (o : ℕ) :
    digestAt (s ++ t) (s.length + o) = digestAt t o := by
  simp only [digestAt, List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _),
    List.nil_append, Nat.add_sub_cancel_left]

theorem digestAt_append_of_isSome {s t : List E} {o : ℕ} (h : (digestAt s o).isSome) :
    digestAt (s ++ t) o = digestAt s o := by
  unfold digestAt at h ⊢
  rcases hd : s.drop o with _ | ⟨x₁, _ | ⟨x₂, rest⟩⟩ <;> rw [hd] at h
  · cases h
  · cases h
  · have ho : o ≤ s.length := by
      by_contra ho
      rw [List.drop_eq_nil_of_le (by omega)] at hd
      cases hd
    rw [List.drop_append_of_le_length ho, hd]
    rfl

/-- Every value a slot reads satisfies `Q`. -/
def AllOut {α : Type} (a : Slot Reading α) (Q : α → Prop) : Prop :=
  ∀ l x r, a.read l = some (x, r) → Q x

theorem allOut_pure {α : Type} {Q : α → Prop} {x : α} (h : Q x) :
    AllOut (Pure.pure x : Slot Reading α) Q := by
  intro l y r hr
  rw [read_pure, Option.some.injEq, Prod.mk.injEq] at hr
  exact hr.1 ▸ h

theorem allOut_bind {α β : Type} {Q : β → Prop} (a : Slot Reading α) {f : α → Slot Reading β}
    (h : ∀ y, AllOut (f y) Q) : AllOut (a >>= f) Q := by
  intro l x r hr
  rw [read_bind, Option.bind_eq_some_iff] at hr
  obtain ⟨⟨y, l₁⟩, -, h₂⟩ := hr
  exact h y _ _ _ h₂

/-- A root read off a history is the digest of its stream's first two scalars. -/
theorem digestAt_of_read_nextRoot {l : List Reading} {d : Digest} {r : List Reading}
    (h : historyOps.nextRoot.read l = some (d, r)) : digestAt (streamOf l) 0 = some d := by
  change ((historyOps.nextScalar >>= fun a ↦ historyOps.nextScalar >>= fun b ↦
    match digestOfScalars (a, b) with
    | some d => Pure.pure d
    | none => Slot.fail).read l) = some (d, r) at h
  rw [read_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨x₁, l₁⟩, h₁, h⟩ := h
  rw [read_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨x₂, l₂⟩, h₂, h⟩ := h
  rw [streamOf_of_read_nextScalar h₁, streamOf_of_read_nextScalar h₂]
  simp only [digestAt, List.drop_zero]
  revert h
  rcases digestOfScalars (x₁, x₂) with _ | d'
  · exact fun h ↦ nomatch h
  · intro h
    rw [read_pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]

/-- The setup's root is the digest at offset `8`. -/
theorem walkSetup_root {l : List Reading} {d : Digest} {r : List Reading}
    (h : (walkSetup historyOps).read l = some (d, r)) : digestAt (streamOf l) 8 = some d := by
  obtain ⟨xs, l₁, -, h₂, s, hs, hl⟩ := read_bind_of_grade (nextScalars_grade historyOps_graded 8) h
  rw [hs, show 8 = s.length + 0 by simp [scalarCounts] at hl; omega, digestAt_append]
  exact digestAt_of_read_nextRoot h₂

/-- A level with a successor reads its root after its fold rounds. -/
theorem walkLevel_root (sh : LevelShape) (hf : sh.final = false) {l : List Reading}
    {lv : WhirLevel} {r : List Reading} (h : (walkLevel historyOps sh).read l = some (lv, r)) :
    ∃ d, lv.root = some d ∧ digestAt (streamOf l) (scalarCounts.folds sh.fold) = some d := by
  simp only [walkLevel, hf, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_map_left] at h
  obtain ⟨folds, l₁, -, h₂, s, hs, hl⟩ :=
    read_bind_of_grade (walkFolds_grade historyOps_graded _) h
  rw [read_bind, Option.bind_eq_some_iff] at h₂
  obtain ⟨⟨d, l₂⟩, h₃, h₄⟩ := h₂
  refine ⟨d, ?_, ?_⟩
  · refine (show AllOut _ fun lv : WhirLevel ↦ lv.root = some d from ?_) _ _ _ h₄
    repeat' refine allOut_bind _ fun _ ↦ ?_
    exact allOut_pure (Q := fun lv : WhirLevel ↦ lv.root = some d) rfl
  · rw [hs, ← hl, show s.length = s.length + 0 from rfl, digestAt_append]
    exact digestAt_of_read_nextRoot h₃

/-- The last level reads no root. -/
theorem walkLevel_root_of_final (sh : LevelShape) (hf : sh.final = true) {l : List Reading}
    {lv : WhirLevel} {r : List Reading} (h : (walkLevel historyOps sh).read l = some (lv, r)) :
    lv.root = none := by
  simp only [walkLevel, hf, ↓reduceIte, pure_bind] at h
  refine (show AllOut _ fun lv : WhirLevel ↦ lv.root = none from ?_) _ _ _ h
  repeat' refine allOut_bind _ fun _ ↦ ?_
  exact allOut_pure (Q := fun lv : WhirLevel ↦ lv.root = none) rfl

theorem levelRootOffsets_add (n : ℕ) : ∀ (o : ℕ) (shs : List LevelShape),
    levelRootOffsets (o + n) shs = (levelRootOffsets o shs).map (· + n)
  | _, [] => rfl
  | o, sh :: shs => by
    rw [levelRootOffsets, levelRootOffsets, List.map_append,
      show o + n + scalarCounts.level sh = o + scalarCounts.level sh + n by omega,
      levelRootOffsets_add n]
    split <;> simp [Nat.add_right_comm]

/-- The levels' roots are the digests at their offsets. -/
theorem walkLevels_roots : ∀ (shs : List LevelShape) {l : List Reading} {ls : List WhirLevel}
    {r : List Reading}, (walkLevels historyOps shs).read l = some (ls, r) →
    (levelRootOffsets 0 shs).map (digestAt (streamOf l)) = (ls.filterMap (·.root)).map some
  | [], l, ls, r, h => by
    rw [walkLevels, read_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | sh :: shs, l, ls, r, h => by
    obtain ⟨lv, l₁, h₁, h₂, s, hs, hl⟩ :=
      read_bind_of_grade (walkLevel_grade historyOps_graded sh) h
    rw [read_bind, Option.bind_eq_some_iff] at h₂
    obtain ⟨⟨ls', l₂⟩, h₃, h₄⟩ := h₂
    rw [read_pure, Option.some.injEq, Prod.mk.injEq] at h₄
    obtain ⟨rfl, -⟩ := h₄
    have ih := walkLevels_roots shs h₃
    rw [levelRootOffsets, show 0 + scalarCounts.level sh = 0 + scalarCounts.level sh from rfl,
      levelRootOffsets_add, List.map_append, List.map_map, List.filterMap_cons]
    have hshift : (digestAt (streamOf l) ∘ fun x ↦ x + scalarCounts.level sh) =
        digestAt (streamOf l₁) := by
      funext o
      simp only [Function.comp, hs, ← hl, Nat.add_comm o, digestAt_append]
    rw [hshift, ih]
    cases hf : sh.final
    · obtain ⟨d, hd, hdig⟩ := walkLevel_root sh hf h₁
      simp [hd, hdig]
    · simp [walkLevel_root_of_final sh hf h₁]


/-- Offsets past a prefix of the stream read the stream after it. -/
theorem map_digestAt_shift {l l₁ : List Reading} {s : List E} (hs : streamOf l = s ++ streamOf l₁)
    (offs : List ℕ) :
    (offs.map (· + s.length)).map (digestAt (streamOf l)) = offs.map (digestAt (streamOf l₁)) := by
  rw [List.map_map]
  refine List.map_congr_left fun o _ ↦ ?_
  simp only [Function.comp, hs, Nat.add_comm o, digestAt_append]

/-- WHIR's opening reads its levels' roots at their offsets, after the first round
polynomial. -/
theorem walkWhir_roots (shs : List LevelShape) {l : List Reading}
    {x : List E × List WhirLevel} {r : List Reading}
    (h : (walkWhir historyOps shs).read l = some (x, r)) :
    (levelRootOffsets 2 shs).map (digestAt (streamOf l)) = (x.2.filterMap (·.root)).map some := by
  obtain ⟨first, l₁, -, h₂, s, hs, hl⟩ :=
    read_bind_of_grade (nextScalars_grade historyOps_graded 2) h
  rw [read_bind, Option.bind_eq_some_iff] at h₂
  obtain ⟨⟨levels, l₂⟩, h₃, h₄⟩ := h₂
  rw [read_pure, Option.some.injEq, Prod.mk.injEq] at h₄
  obtain ⟨rfl, -⟩ := h₄
  have hl' : s.length = 2 := by simpa [scalarCounts] using hl
  rw [show 2 = 0 + s.length by omega, levelRootOffsets_add, map_digestAt_shift hs]
  exact walkLevels_roots shs h₃

/-- **The chain walk's roots** on a history are the digests of the history's stream at the root
offsets, all present: the level-0 root, then the levels' roots in order. -/
theorem walkChain_roots {prog : Program} {s : Sizes} {input : PublicInput}
    {shs : List LevelShape} {l : List Reading} {w : Wire} {r : List Reading}
    (h : (walkChain historyOps prog s input shs).read l = some (w, r)) :
    (rootOffsets prog s input shs).map (digestAt (streamOf l)) =
      (w.root :: w.whir.filterMap (·.root)).map some := by
  rw [walkChain_eq_setup] at h
  obtain ⟨d, l₁, h₁, h₂, s₁, hs₁, hl₁⟩ := read_bind_of_grade (walkSetup_grade historyOps_graded) h
  simp only [walkAfterSetup] at h₂
  obtain ⟨_, l₂, -, h₃, s₂, hs₂, hl₂⟩ :=
    read_bind_of_grade (walkBus_grade historyOps_graded _ _) h₂
  obtain ⟨_, l₃, -, h₄, s₃, hs₃, hl₃⟩ :=
    read_bind_of_grade (walkTables_grade historyOps_graded _ _) h₃
  obtain ⟨_, l₄, -, h₅, s₄, hs₄, hl₄⟩ := read_bind_of_grade (walkPub_grade historyOps_graded _) h₄
  obtain ⟨_, l₅, -, h₆, s₅, hs₅, hl₅⟩ := read_bind_of_grade (walkFlock_grade historyOps_graded _) h₅
  obtain ⟨_, l₆, -, h₇, s₆, hs₆, hl₆⟩ := read_bind_of_grade historyOps_graded.sample h₆
  rw [read_bind, Option.bind_eq_some_iff] at h₇
  obtain ⟨⟨⟨first, levels⟩, l₇⟩, h₈, h₉⟩ := h₇
  rw [read_pure, Option.some.injEq, Prod.mk.injEq] at h₉
  obtain ⟨rfl, -⟩ := h₉
  have hS : streamOf l = (s₁ ++ s₂ ++ s₃ ++ s₄ ++ s₅ ++ s₆) ++ streamOf l₆ := by
    rw [hs₁, hs₂, hs₃, hs₄, hs₅, hs₆]
    simp only [List.append_assoc]
  have hstart : whirStart prog s input = 2 + (s₁ ++ s₂ ++ s₃ ++ s₄ ++ s₅ ++ s₆).length := by
    simp only [whirStart, List.length_append, hl₁, hl₂, hl₃, hl₄, hl₅, hl₆, scalarCounts]
    omega
  rw [rootOffsets, List.map_cons, hstart, levelRootOffsets_add, map_digestAt_shift hS,
    walkWhir_roots shs h₈, walkSetup_root h₁]
  rfl

/-- A list of offsets whose digests are all present reads them all. -/
theorem filterMap_of_map_eq {f : ℕ → Option Digest} :
    ∀ {offs : List ℕ} {L : List Digest}, offs.map f = L.map some → offs.filterMap f = L
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | o :: offs, d :: L, h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    rw [List.filterMap_cons, h.1, filterMap_of_map_eq h.2]

/-- **The roots the verifier's walk reads are the proof's roots**: if the chain walk of the
verifier, its steps logged, succeeds on a proof at the sizes, rate and levels it announces, the
roots it reads are `rootsOf prog input proof`, in order. -/
theorem rootsOf_eq_of_walkChainLogged {prog : Program} {input : PublicInput}
    {proof : Proof PrunedMerklePaths} {s : Sizes} {ρ : ℕ} {levels : List Whir.Level}
    {H : List UInt8 → Id Digest} {st' : ReaderState PrunedMerklePaths} {w : Wire}
    {hist : List Reading} (hs : setup? prog proof = some (s, ρ))
    (hl : ladderOf prog s ρ = some levels)
    (h : walkChainLogged prog s input (levelShapes (stackMu prog s) levels) H
      ⟨FsState.seed prog input, proof.stream, proof.merkle⟩ = .ok ((w, hist), st')) :
    rootsOf prog input proof = w.root :: w.whir.filterMap (·.root) := by
  obtain ⟨hw, hst⟩ := walkChain_history H h
  have hr := walkChain_roots hw
  unfold rootsOf
  rw [hs]
  simp only [hl]
  refine filterMap_of_map_eq ?_
  rw [← hr]
  simp only at hst
  rw [hst]
  refine List.map_congr_left fun o ho ↦ digestAt_append_of_isSome ?_
  have hmem : digestAt (streamOf hist) o ∈ (w.root :: w.whir.filterMap (·.root)).map some :=
    hr ▸ List.mem_map_of_mem ho
  obtain ⟨d, -, hd⟩ := List.mem_map.mp hmem
  rw [← hd]
  rfl

end Walk

end ProofRoots

end

end LeanerVM.Protocol
