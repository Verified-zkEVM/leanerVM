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
`proofDigests = 6` (`length_rootsOf_le`): a root per level, the deployed ladders having at most six
levels (six at `μ = 28`, the largest stack).

`walkChain_roots`: the roots the chain walk reads on a history are the digests of the history's
stream at the offsets, all present; `rootsOf_eq_of_walkChainLogged`: the roots the verifier's
chain walk reads on a proof, its steps logged, are `rootsOf prog input proof`, in order.

The same offsets counted in readings rather than scalars (`readingCounts`: a challenge and a nonce
one reading each) locate the roots on the history itself: `walkChain_rootAt`, the roots at the
reading offsets (`rootAt`) are the walk's, and a prefix reads the roots it carries whole
(`rootAt_prefix`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa Verify DecodeChain

@[expose] public section

namespace ProofRoots

/-- The stream's scalars each primitive reads: a scalar one, a challenge none, a root two, a
nonce one. -/
def scalarCounts : StepCounts := ⟨1, 0, 2, fun _ ↦ 1⟩

/-- The offsets of the roots the levels `shs` read, counted by `c`, the first level starting at
offset `o`: one per level with a successor, after its fold rounds. -/
def levelRootOffsets (c : StepCounts) : ℕ → List LevelShape → List ℕ
  | _, [] => []
  | o, sh :: shs => (if sh.final then [] else [o + c.folds sh.fold]) ++
      levelRootOffsets c (o + c.level sh) shs

/-- The offset, counted by `c`, at which WHIR's levels start: after the setup, the four front
phases and the first round polynomial. -/
def whirStart (c : StepCounts) (prog : Program) (s : Sizes) (input : PublicInput) : ℕ :=
  c.setup + c.bus (leanVm prog s).μBus (leanVm prog s).busClaims +
    c.tables (leanVm prog s).τmax (leanVm prog s).tableColumns +
    c.pub (PublicInput.sentCount (leanVm prog s) ((leanVm prog s).publicLines input)) +
    c.flock (s.τ 5) + c.sample + 2 * c.scalar

/-- The offsets, counted by `c`, of the roots the chain walk reads: the level-0 root after the
eight announced sizes, then the later levels' roots. -/
def rootOffsets (c : StepCounts) (prog : Program) (s : Sizes) (input : PublicInput)
    (shs : List LevelShape) : List ℕ :=
  8 * c.scalar :: levelRootOffsets c (whirStart c prog s input) shs

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
      (rootOffsets scalarCounts prog s input (levelShapes (stackMu prog s) levels)).filterMap
        (digestAt proof.stream)

/-- One root per level with a successor. -/
private theorem length_levelRootOffsets (c : StepCounts) : ∀ (o : ℕ) (shs : List LevelShape),
    (levelRootOffsets c o shs).length = (shs.filter fun sh ↦ !sh.final).length
  | _, [] => rfl
  | o, sh :: shs => by
    rw [levelRootOffsets, List.length_append, length_levelRootOffsets, List.filter_cons]
    cases sh.final <;> simp [Nat.add_comm]

/-- A ladder's levels all have a successor but the last. -/
private theorem length_filter_levelShapes : ∀ (μ : ℕ) (levels : List Whir.Level),
    ((levelShapes μ levels).filter fun sh ↦ !sh.final).length = levels.length - 1
  | _, [] => rfl
  | _, [_] => rfl
  | μ, l :: l' :: ls => by
    have ih := length_filter_levelShapes (μ - l.fold) (l' :: ls)
    simp only [levelShapes, List.filter_cons, Bool.not_false, ↓reduceIte, List.length_cons, ih]
    simp

/-- The deployed ladders have at most six levels. -/
private theorem length_ladder_le {μ ρ : ℕ} {levels : List Whir.Level}
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

/-- The slots that read exactly a prefix of measure `n`, by an additive `len`, wherever they
read. -/
def measureGrade (len : List Reading → ℕ) (hlen : ∀ a b, len (a ++ b) = len a + len b) :
    MonadGrade (Slot Reading) where
  P a n := ∀ l x r, a.read l = some (x, r) → ∃ c, l = c ++ r ∧ len c = n
  pure x l y r h := by
    rw [read_pure, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], by simp [h.2], by simpa using hlen [] []⟩
  bind {α β a f n k} ha hf l x r h := by
    rw [read_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨y, l₁⟩, h₁, h₂⟩ := h
    obtain ⟨c₁, rfl, hc₁⟩ := ha _ _ _ h₁
    obtain ⟨c₂, rfl, hc₂⟩ := hf y _ _ _ h₂
    exact ⟨c₁ ++ c₂, by simp, by rw [hlen, hc₁, hc₂]⟩

/-- The slots that read exactly `n` readings wherever they read. -/
def readGrade : MonadGrade (Slot Reading) := measureGrade List.length fun _ _ ↦ List.length_append

/-- Every value a slot reads satisfies `Q`. -/
private def AllOut {α : Type} (a : Slot Reading α) (Q : α → Prop) : Prop :=
  ∀ l x r, a.read l = some (x, r) → Q x

private theorem allOut_pure {α : Type} {Q : α → Prop} {x : α} (h : Q x) :
    AllOut (Pure.pure x : Slot Reading α) Q := by
  intro l y r hr
  rw [read_pure, Option.some.injEq, Prod.mk.injEq] at hr
  exact hr.1 ▸ h

private theorem allOut_bind {α β : Type} {Q : β → Prop} (a : Slot Reading α)
    {f : α → Slot Reading β} (h : ∀ y, AllOut (f y) Q) : AllOut (a >>= f) Q := by
  intro l x r hr
  rw [read_bind, Option.bind_eq_some_iff] at hr
  obtain ⟨⟨y, l₁⟩, -, h₂⟩ := hr
  exact h y _ _ _ h₂

/-- The last level reads no root. -/
private theorem walkLevel_root_of_final (sh : LevelShape) (hf : sh.final = true)
    {l : List Reading} {lv : WhirLevel} {r : List Reading}
    (h : (walkLevel historyOps sh).read l = some (lv, r)) : lv.root = none := by
  simp only [walkLevel, hf, ↓reduceIte, pure_bind] at h
  refine (show AllOut _ fun lv : WhirLevel ↦ lv.root = none from ?_) _ _ _ h
  repeat' refine allOut_bind _ fun _ ↦ ?_
  exact allOut_pure (Q := fun lv : WhirLevel ↦ lv.root = none) rfl

private theorem levelRootOffsets_add (c : StepCounts) (n : ℕ) :
    ∀ (o : ℕ) (shs : List LevelShape),
      levelRootOffsets c (o + n) shs = (levelRootOffsets c o shs).map (· + n)
  | _, [] => rfl
  | o, sh :: shs => by
    rw [levelRootOffsets, levelRootOffsets, List.map_append,
      show o + n + c.level sh = o + c.level sh + n by omega,
      levelRootOffsets_add c n]
    split <;> simp [Nat.add_right_comm]

/-! ### The roots at their offsets, by an additive measure of the readings -/

section Measure

variable {len : List Reading → ℕ} {hlen : ∀ a b, len (a ++ b) = len a + len b}

private theorem next_measure {β : Type} {f : Reading → Option β} {k : ℕ}
    (hf : ∀ a y, f a = some y → len [a] = k) : (measureGrade len hlen).P (Slot.next f) k := by
  rintro (_ | ⟨a, l⟩) x r h
  · exact nomatch h
  · rw [read_next_cons, Option.map_eq_some_iff] at h
    obtain ⟨y, hy, he⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨[a], rfl, hf a y hy⟩

/-- The history reader's primitives, counted by a measure of their readings, a root's count two
scalars'. -/
private theorem historyOps_measured (c : StepCounts)
    (hs : ∀ a y, scalarOf a = some y → len [a] = c.scalar)
    (hc : ∀ a y, challengeOf a = some y → len [a] = c.sample)
    (hn : ∀ a y bits, nonceOf a = some y → len [a] = c.pow bits)
    (hr : c.root = c.scalar + c.scalar) :
    ChainOps.Graded (measureGrade len hlen) historyOps c where
  nextScalar := next_measure hs
  sample := next_measure hc
  nextRoot := (measureGrade len hlen).of_eq ((measureGrade len hlen).bind (next_measure hs)
    fun _ ↦ (measureGrade len hlen).bind (k := 0) (next_measure hs) fun _ ↦ by
      split
      · exact (measureGrade len hlen).pure _
      · exact fun _ _ _ h ↦ nomatch h) (by omega)
  checkPow bits := next_measure fun a y h ↦ hn a y bits h

/-- A graded slot reads a prefix of exactly its count. -/
private theorem read_bind_of_measure {α β : Type} {a : Slot Reading α} {f : α → Slot Reading β}
    {n : ℕ} (ha : (measureGrade len hlen).P a n) {l : List Reading} {x : β} {r : List Reading}
    (h : (a >>= f).read l = some (x, r)) :
    ∃ y l₁, a.read l = some (y, l₁) ∧ (f y).read l₁ = some (x, r) ∧
      ∃ c, l = c ++ l₁ ∧ len c = n := by
  rw [read_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨y, l₁⟩, h₁, h₂⟩ := h
  obtain ⟨c, rfl, hc⟩ := ha _ _ _ h₁
  exact ⟨y, l₁, h₁, h₂, c, rfl, hc⟩

variable {pos : List Reading → ℕ → Option Digest}
  (hpos : ∀ c l o, pos (c ++ l) (len c + o) = pos l o)
  (hroot : ∀ {l d r}, historyOps.nextRoot.read l = some (d, r) → pos l 0 = some d)
  {c : StepCounts} (hg : ChainOps.Graded (measureGrade len hlen) historyOps c)
include hpos hroot hg

omit hroot hg in
/-- Offsets past a prefix read the history after it. -/
private theorem map_pos_shift (c₀ l : List Reading) (offs : List ℕ) :
    (offs.map (· + len c₀)).map (pos (c₀ ++ l)) = offs.map (pos l) := by
  rw [List.map_map]
  exact List.map_congr_left fun o _ ↦ by simp only [Function.comp, Nat.add_comm o, hpos]

/-- The setup's root is at offset `8` scalars. -/
private theorem walkSetup_pos {l : List Reading} {d : Digest} {r : List Reading}
    (h : (walkSetup historyOps).read l = some (d, r)) : pos l (8 * c.scalar) = some d := by
  obtain ⟨xs, l₁, -, h₂, c₀, rfl, hc⟩ := read_bind_of_measure (nextScalars_grade hg 8) h
  rw [← hc, ← Nat.add_zero (len c₀), hpos]
  exact hroot h₂

/-- A level with a successor reads its root after its fold rounds. -/
private theorem walkLevel_pos (sh : LevelShape) (hf : sh.final = false) {l : List Reading}
    {lv : WhirLevel} {r : List Reading} (h : (walkLevel historyOps sh).read l = some (lv, r)) :
    ∃ d, lv.root = some d ∧ pos l (c.folds sh.fold) = some d := by
  simp only [walkLevel, hf, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_map_left] at h
  obtain ⟨folds, l₁, -, h₂, c₀, rfl, hc⟩ := read_bind_of_measure (walkFolds_grade hg _) h
  rw [read_bind, Option.bind_eq_some_iff] at h₂
  obtain ⟨⟨d, l₂⟩, h₃, h₄⟩ := h₂
  refine ⟨d, ?_, ?_⟩
  · refine (show AllOut _ fun lv : WhirLevel ↦ lv.root = some d from ?_) _ _ _ h₄
    repeat' refine allOut_bind _ fun _ ↦ ?_
    exact allOut_pure (Q := fun lv : WhirLevel ↦ lv.root = some d) rfl
  · rw [← hc, ← Nat.add_zero (len c₀), hpos]
    exact hroot h₃

/-- The levels' roots are at their offsets. -/
private theorem walkLevels_pos : ∀ (shs : List LevelShape) {l : List Reading}
    {ls : List WhirLevel} {r : List Reading}, (walkLevels historyOps shs).read l = some (ls, r) →
    (levelRootOffsets c 0 shs).map (pos l) = (ls.filterMap (·.root)).map some
  | [], l, ls, r, h => by
    rw [walkLevels, read_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | sh :: shs, l, ls, r, h => by
    obtain ⟨lv, l₁, h₁, h₂, c₀, rfl, hc⟩ := read_bind_of_measure (walkLevel_grade hg sh) h
    rw [read_bind, Option.bind_eq_some_iff] at h₂
    obtain ⟨⟨ls', l₂⟩, h₃, h₄⟩ := h₂
    rw [read_pure, Option.some.injEq, Prod.mk.injEq] at h₄
    obtain ⟨rfl, -⟩ := h₄
    rw [levelRootOffsets, show 0 + c.level sh = 0 + len c₀ by rw [hc], levelRootOffsets_add,
      List.map_append, map_pos_shift hpos, walkLevels_pos shs h₃, List.filterMap_cons]
    cases hf : sh.final
    · obtain ⟨d, hd, hdig⟩ := walkLevel_pos hpos hroot hg sh hf h₁
      simp [hd, hdig]
    · simp [walkLevel_root_of_final sh hf h₁]

/-- WHIR's opening reads its levels' roots at their offsets, after the first round polynomial. -/
private theorem walkWhir_pos (shs : List LevelShape) {l : List Reading}
    {x : List E × List WhirLevel} {r : List Reading}
    (h : (walkWhir historyOps shs).read l = some (x, r)) :
    (levelRootOffsets c (2 * c.scalar) shs).map (pos l) = (x.2.filterMap (·.root)).map some := by
  obtain ⟨first, l₁, -, h₂, c₀, rfl, hc⟩ := read_bind_of_measure (nextScalars_grade hg 2) h
  rw [read_bind, Option.bind_eq_some_iff] at h₂
  obtain ⟨⟨levels, l₂⟩, h₃, h₄⟩ := h₂
  rw [read_pure, Option.some.injEq, Prod.mk.injEq] at h₄
  obtain ⟨rfl, -⟩ := h₄
  rw [← hc, ← Nat.zero_add (len c₀), levelRootOffsets_add, map_pos_shift hpos]
  exact walkLevels_pos hpos hroot hg shs h₃

/-- The chain walk's roots on a history are at the root offsets, all present: the level-0 root,
then the levels' roots in order. -/
private theorem walkChain_pos {prog : Program} {s : Sizes} {input : PublicInput}
    {shs : List LevelShape} {l : List Reading} {w : Wire} {r : List Reading}
    (h : (walkChain historyOps prog s input shs).read l = some (w, r)) :
    (rootOffsets c prog s input shs).map (pos l) =
      (w.root :: w.whir.filterMap (·.root)).map some := by
  rw [walkChain_eq_setup] at h
  obtain ⟨d, l₁, h₁, h₂, c₁, rfl, hc₁⟩ := read_bind_of_measure (walkSetup_grade hg) h
  simp only [walkAfterSetup] at h₂
  obtain ⟨_, l₂, -, h₃, c₂, rfl, hc₂⟩ := read_bind_of_measure (walkBus_grade hg _ _) h₂
  obtain ⟨_, l₃, -, h₄, c₃, rfl, hc₃⟩ := read_bind_of_measure (walkTables_grade hg _ _) h₃
  obtain ⟨_, l₄, -, h₅, c₄, rfl, hc₄⟩ := read_bind_of_measure (walkPub_grade hg _) h₄
  obtain ⟨_, l₅, -, h₆, c₅, rfl, hc₅⟩ := read_bind_of_measure (walkFlock_grade hg _) h₅
  obtain ⟨_, l₆, -, h₇, c₆, rfl, hc₆⟩ := read_bind_of_measure hg.sample h₆
  rw [read_bind, Option.bind_eq_some_iff] at h₇
  obtain ⟨⟨⟨first, levels⟩, l₇⟩, h₈, h₉⟩ := h₇
  rw [read_pure, Option.some.injEq, Prod.mk.injEq] at h₉
  obtain ⟨rfl, -⟩ := h₉
  have hstart : whirStart c prog s input =
      2 * c.scalar + len (c₁ ++ c₂ ++ c₃ ++ c₄ ++ c₅ ++ c₆) := by
    simp only [whirStart, hlen, hc₁, hc₂, hc₃, hc₄, hc₅, hc₆]
    omega
  rw [rootOffsets, List.map_cons, walkSetup_pos hpos hroot hg h₁, hstart, levelRootOffsets_add,
    show c₁ ++ (c₂ ++ (c₃ ++ (c₄ ++ (c₅ ++ (c₆ ++ l₆))))) =
      c₁ ++ c₂ ++ c₃ ++ c₄ ++ c₅ ++ c₆ ++ l₆ by simp only [List.append_assoc],
    map_pos_shift hpos, walkWhir_pos hpos hroot hg shs h₈]
  rfl

end Measure

/-! ### The roots in the stream -/

private theorem digestAt_append (s t : List E) (o : ℕ) :
    digestAt (s ++ t) (s.length + o) = digestAt t o := by
  simp only [digestAt, List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _),
    List.nil_append, Nat.add_sub_cancel_left]

private theorem digestAt_append_of_isSome {s t : List E} {o : ℕ} (h : (digestAt s o).isSome) :
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

/-- A root read off a history is the digest of its stream's first two scalars. -/
private theorem digestAt_of_read_nextRoot {l : List Reading} {d : Digest} {r : List Reading}
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

/-- **The chain walk's roots** on a history are the digests of the history's stream at the root
offsets, all present: the level-0 root, then the levels' roots in order. -/
private theorem walkChain_roots {prog : Program} {s : Sizes} {input : PublicInput}
    {shs : List LevelShape} {l : List Reading} {w : Wire} {r : List Reading}
    (h : (walkChain historyOps prog s input shs).read l = some (w, r)) :
    (rootOffsets scalarCounts prog s input shs).map (digestAt (streamOf l)) =
      (w.root :: w.whir.filterMap (·.root)).map some :=
  walkChain_pos (len := fun c ↦ (streamOf c).length)
    (hlen := fun a b ↦ by rw [streamOf_append, List.length_append])
    (fun c l o ↦ by rw [streamOf_append, digestAt_append]) digestAt_of_read_nextRoot
    (historyOps_measured scalarCounts
      (fun ⟨b, _⟩ y h ↦ by cases b <;> simp_all [scalarOf, streamOf, scalarCounts])
      (fun ⟨b, _⟩ y h ↦ by cases b <;> simp_all [challengeOf, streamOf, scalarCounts])
      (fun ⟨b, _⟩ y _ h ↦ by cases b <;> simp_all [nonceOf, streamOf, scalarCounts]) rfl) h

/-- A list of offsets whose digests are all present reads them all. -/
private theorem filterMap_of_map_eq {f : ℕ → Option Digest} :
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

/-! ## The roots the walk reads, by readings -/

/-- The readings each primitive takes: a scalar one, a challenge one, a root two, a nonce one. -/
def readingCounts : StepCounts := ⟨1, 1, 2, fun _ ↦ 1⟩

/-- The root a history carries at reading `o`: two observes there, read as a digest. -/
def rootAt (hist : List Reading) (o : ℕ) : Option Digest :=
  match hist[o]?, hist[o + 1]? with
  | some (.observe x₁, _), some (.observe x₂, _) => digestOfScalars (x₁, x₂)
  | _, _ => none

theorem rootAt_cons_succ (a : Reading) (hist : List Reading) (o : ℕ) :
    rootAt (a :: hist) (o + 1) = rootAt hist o := rfl

/-- Offsets past a prefix read the history after it. -/
private theorem rootAt_append (c l : List Reading) (o : ℕ) :
    rootAt (c ++ l) (c.length + o) = rootAt l o := by
  induction c with
  | nil => rw [List.nil_append, List.length_nil, Nat.zero_add]
  | cons a c ih =>
    rw [List.cons_append, List.length_cons, show c.length + 1 + o = c.length + o + 1 by omega,
      rootAt_cons_succ, ih]

/-- **A prefix reads the roots it carries whole.** -/
theorem rootAt_prefix (hs rest : List Reading) {o : ℕ} (h : o + 1 < hs.length) :
    rootAt (hs ++ rest) o = rootAt hs o := by
  simp only [rootAt, List.getElem?_append_left (show o < hs.length by omega),
    List.getElem?_append_left h]

/-- **The history reader's primitives, counted** in the readings they take. -/
theorem historyOps_readGraded : ChainOps.Graded readGrade historyOps readingCounts :=
  historyOps_measured readingCounts (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) rfl

/-- A scalar read off a history is an observe step's. -/
private theorem eq_of_read_nextScalar {l : List Reading} {x : E} {r : List Reading}
    (h : historyOps.nextScalar.read l = some (x, r)) : ∃ e, l = (.observe x, e) :: r := by
  rcases l with _ | ⟨⟨b, e⟩, l⟩
  · exact nomatch h
  · change (scalarOf (b, e)).map (·, l) = some (x, r) at h
    cases b with
    | observe y =>
      simp only [scalarOf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨e, rfl⟩
    | squeeze => exact nomatch h
    | nonce _ => exact nomatch h

/-- A root read off a history is the root at its first reading. -/
private theorem rootAt_of_read_nextRoot {l : List Reading} {d : Digest} {r : List Reading}
    (h : historyOps.nextRoot.read l = some (d, r)) : rootAt l 0 = some d := by
  change ((historyOps.nextScalar >>= fun a ↦ historyOps.nextScalar >>= fun b ↦
    match digestOfScalars (a, b) with
    | some d => Pure.pure d
    | none => Slot.fail).read l) = some (d, r) at h
  rw [read_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨x₁, l₁⟩, h₁, h⟩ := h
  rw [read_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨x₂, l₂⟩, h₂, h⟩ := h
  obtain ⟨e₁, rfl⟩ := eq_of_read_nextScalar h₁
  obtain ⟨e₂, rfl⟩ := eq_of_read_nextScalar h₂
  show digestOfScalars (x₁, x₂) = some d
  revert h
  rcases digestOfScalars (x₁, x₂) with _ | d'
  · exact fun h ↦ nomatch h
  · intro h
    rw [read_pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]

/-- **The chain walk's roots, by readings**: on a history the chain walk reads, the roots at the
reading offsets are the roots the walk reads, all present: the level-0 root, then the levels' roots
in order. These are the offsets `wordsOf` reads the words' roots at. -/
theorem walkChain_rootAt {prog : Program} {s : Sizes} {input : PublicInput}
    {shs : List LevelShape} {l : List Reading} {w : Wire} {r : List Reading}
    (h : (walkChain historyOps prog s input shs).read l = some (w, r)) :
    (rootOffsets readingCounts prog s input shs).map (rootAt l) =
      (w.root :: w.whir.filterMap (·.root)).map some :=
  walkChain_pos rootAt_append rootAt_of_read_nextRoot historyOps_readGraded h

end Walk

end ProofRoots

end

end LeanerVM.Protocol
