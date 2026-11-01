module

public import LeanVM.Protocol.Extraction.Extractor

/-!
# The stack's root, without the verifier's free monad

The extractor starts from `afterRoot` (`Statement/Extractor.lean`): the verifier's steps 1 and 2,
`announceSizesAndRoot`, a `Prog` run by `runPure` (every permutation answered by `default`).
`Prog`'s constructors hold continuations (`read : (E → Prog α) → Prog α`, …), which the cost
compiler does not take. Here the same steps are plain state-passing functions in `Option`:

* `absorbPure`: the sponge's `absorb` with every permutation `default`; `readPure n`: read and
  absorb `n` scalars (`runPure_readScalars`); `commitPure`: read a root (`runPure_readCommitment`);
* `readSizesPure`, `commitStackPure`: `readSizes` and `commitStack` (`runPure_readSizes`,
  `runPure_commitStack`);
* **`afterRootDirect_eq`**: `afterRootDirect` is `afterRoot`.

The lighter layout: the extractor reads of the layout only `logMemory`, `logBytecode`,
`placements`, `stackLog` and `tableLogHeights`. `buildLayoutLite` computes only these (no bus
blocks, no forms, no bytecode copy), and is `buildLayout` followed by `layoutLite`
(`buildLayoutLite_eq`); `afterRootLite` is `afterRoot` with its layout so cut
(`afterRootLite_eq`).

The run's algebra: `runPure_bind` (a sequence runs as its first program, then the continuation),
`runPure_require_bind`, `runPure_liftOption_bind`, `runPure_readScalars_bind`, `runPure_pure`.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Parameters.Whir LeanVM.Protocol.KeccakHash LeanVM.Extraction

public section

/-! ## The run's algebra -/

/-- `runPure` without `Id.run`: the run with every permutation answered by `default`. -/
abbrev runDefault {α : Type} (p : Prog α) (s : ProgState) : Option (α × ProgState) :=
  Compile.run (m := Id) (fun _ ↦ default) p s

/-- A sequence runs as its first program, then the continuation on the first's value. -/
theorem runDefault_bind {α β : Type} (p : Prog α) (f : α → Prog β) (s : ProgState) :
    runDefault (p.bind f) s = (runDefault p s).bind fun r ↦ runDefault (f r.1) r.2 := by
  induction p generalizing s with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    simp only [runDefault, Prog.bind, Compile.run]
    split
    · rfl
    · exact ih _ _
  | sample k ih => exact ih _ _
  | grind b k ih =>
    simp only [runDefault, Prog.bind, Compile.run]
    split
    · rfl
    · simp only [bind, pure]
      split
      · exact ih _
      · rfl
  | commit h w k ih =>
    simp only [runDefault, Prog.bind, Compile.run]
    split
    · simp only [bind]
      split
      · exact ih _
      · rfl
    · rfl
  | query i ps k ih =>
    simp only [runDefault, Prog.bind, Compile.run]
    split
    · rfl
    · simp only [bind]
      split
      · exact ih _ _
      · rfl

/-- **`runPure` of a sequence**: the first program's run, then the continuation's. -/
theorem runPure_bind {α β : Type} (p : Prog α) (f : α → Prog β) (s : ProgState) :
    runPure (p >>= f) s = (runPure p s).bind fun r ↦ runPure (f r.1) r.2 :=
  runDefault_bind p f s

theorem runPure_bind_of_some {α β : Type} {p : Prog α} {f : α → Prog β} {s s' : ProgState}
    {a : α} (h : runPure p s = some (a, s')) : runPure (p >>= f) s = runPure (f a) s' := by
  have := runPure_bind p f s
  rw [h] at this
  exact this

theorem runPure_bind_of_none {α β : Type} {p : Prog α} {f : α → Prog β} {s : ProgState}
    (h : runPure p s = none) : runPure (p >>= f) s = none := by
  have := runPure_bind p f s
  rw [h] at this
  exact this

theorem runPure_pure {α : Type} (a : α) (s : ProgState) :
    runPure (pure a : Prog α) s = some (a, s) := rfl

theorem runPure_require_bind {β : Type} (c : Prop) [Decidable c] (f : Unit → Prog β)
    (s : ProgState) :
    runPure (Prog.require c >>= f) s = if c then runPure (f ()) s else none := by
  by_cases hc : c
  · simp only [Prog.require, hc, ↓reduceIte]; rfl
  · simp only [Prog.require, hc, ↓reduceIte]; rfl

theorem runPure_liftOption_bind {α β : Type} (o : Option α) (f : α → Prog β) (s : ProgState) :
    runPure (liftOption o >>= f) s = o.bind fun a ↦ runPure (f a) s := by
  cases o <;> rfl

/-! ## The sponge and the reads -/

/-- `absorb` with every permutation answered by `default`: a full queue is replaced by the
default state with an empty queue, then the scalar joins the queue. -/
@[expose] def absorbPure (sp : Compile.Sponge) (x : E) (tag : ℕ) : Compile.Sponge :=
  let sp : Compile.Sponge := if sp.pending.length = rateScalars then ⟨default, []⟩ else sp
  { sp with pending := sp.pending ++ [(x, tag)] }

/-- Read `n` prover scalars, each absorbed with `dsObserve` (`Prog.readScalars`). -/
@[expose] def readPure : ℕ → ProgState → Option (List E × ProgState)
  | 0, s => some ([], s)
  | n + 1, s =>
    match s.stream with
    | [] => none
    | x :: xs =>
      (readPure n { s with sponge := absorbPure s.sponge x dsObserve, stream := xs }).map
        fun r ↦ (x :: r.1, r.2)

/-- **`readScalars`, run**, is `readPure`. -/
theorem runPure_readScalars (n : ℕ) (s : ProgState) :
    runPure (Prog.readScalars n) s = readPure n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rcases s with ⟨sp, _ | ⟨x, xs⟩, os, roots⟩
    · rfl
    · have h1 : runPure Prog.readScalar ⟨sp, x :: xs, os, roots⟩ =
          some (x, ⟨absorbPure sp x dsObserve, xs, os, roots⟩) := by
        simp only [runPure, Prog.readScalar, Compile.run, Compile.absorb, Compile.duplex,
          absorbPure]
        split <;> rfl
      show runPure (Prog.readScalar >>= fun y ↦ Prog.readScalars n >>= fun ys ↦ pure (y :: ys))
        ⟨sp, x :: xs, os, roots⟩ = _
      rw [runPure_bind_of_some h1, runPure_bind, ih]
      show _ = (readPure n ⟨absorbPure sp x dsObserve, xs, os, roots⟩).map fun r ↦ (x :: r.1, r.2)
      cases readPure n ⟨absorbPure sp x dsObserve, xs, os, roots⟩ <;> rfl

theorem runPure_readScalars_bind {β : Type} (n : ℕ) (f : List E → Prog β) (s : ProgState) :
    runPure (Prog.readScalars n >>= f) s = (readPure n s).bind fun r ↦ runPure (f r.1) r.2 := by
  rw [runPure_bind, runPure_readScalars]

/-- Read a root (`Prog.readCommitment height width`): two scalars, absorbed, which must encode a
digest; the root is recorded with its shape. -/
@[expose] def commitPure (height width : ℕ) (s : ProgState) : Option (Unit × ProgState) :=
  match s.stream with
  | x0 :: x1 :: xs =>
    match digestOfScalars (x0, x1) with
    | some root =>
      some ((), { s with
        sponge := absorbPure (absorbPure s.sponge x0 dsObserve) x1 dsObserve
        stream := xs
        roots := s.roots ++ [(root, height, width)] })
    | none => none
  | _ => none

theorem runPure_readCommitment (height width : ℕ) (s : ProgState) :
    runPure (Prog.readCommitment height width) s = commitPure height width s := by
  rcases s with ⟨sp, _ | ⟨x0, _ | ⟨x1, xs⟩⟩, os, roots⟩
  · simp only [runPure, Prog.readCommitment, Compile.run, commitPure]; rfl
  · simp only [runPure, Prog.readCommitment, Compile.run, commitPure]; rfl
  · simp only [runPure, Prog.readCommitment, Compile.run, commitPure, Compile.absorb,
      Compile.duplex, absorbPure]
    cases digestOfScalars (x0, x1)
    · simp [Id.run, bind, pure]
    · simp [Id.run, bind, pure]
      split_ifs <;> simp_all

/-! ## Steps 1 and 2 -/

/-- `readSizes bytecode` (`Statement/LeanVmVerifier.lean`), run: the announced sizes, read and
checked, and the layout they give. -/
@[expose] def readSizesPure (bytecode : List K) (s : ProgState) :
    Option ((Layout × ℕ) × ProgState) :=
  (readPure (2 + tables.length) s).bind fun r ↦
    if (r.1.all fun value ↦ value.limb 1 = 0 ∧ value.limb 2 = 0) then
      let logMemory := kToNat ((r.1.headD 0).limb 0)
      let tableRows := ((r.1.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)
      let logInverseRate := kToNat ((r.1.getLastD 0).limb 0)
      if 1 ≤ logInverseRate ∧ logInverseRate ≤ 4 then
        (buildLayout bytecode logMemory tableRows).bind fun layout ↦
          if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
            some ((layout, logInverseRate), r.2)
          else none
      else none
    else none

theorem runPure_readSizes (bytecode : List K) (s : ProgState) :
    runPure (readSizes bytecode) s = readSizesPure bytecode s := by
  simp only [readSizes, readSizesPure, runPure_readScalars_bind, runPure_require_bind,
    runPure_liftOption_bind, runPure_pure]

/-- `commitStack logN logInvRate`, run: the stack's root, at the shape of the ladder's first
level. -/
@[expose] def commitStackPure (logN logInvRate : ℕ) (s : ProgState) : Option (Unit × ProgState) :=
  match Whir.ladder logN logInvRate with
  | some (level :: _) => commitPure (logN - level.fold + level.logInvRate) (2 ^ level.fold) s
  | _ => none

theorem runPure_commitStack (logN logInvRate : ℕ) (s : ProgState) :
    runPure (commitStack logN logInvRate) s = commitStackPure logN logInvRate s := by
  unfold commitStack commitStackPure
  cases Whir.ladder logN logInvRate with
  | none => rfl
  | some config =>
    cases config with
    | nil => rfl
    | cons level _ =>
      exact runPure_readCommitment (logN - level.fold + level.logInvRate) (2 ^ level.fold) s

/-- The verifier's state at the start: the sponge's default state, the proof unread, no root. -/
@[expose] def initialState (π : Proof) : ProgState := ⟨⟨default, []⟩, π.stream, π.openings, []⟩

/-- **`afterRoot`, direct**: the announced sizes, then the stack's root. -/
@[expose] def afterRootDirect (bytecode : List K) (π : Proof) :
    Option ((Layout × ℕ) × ProgState) :=
  (readSizesPure bytecode (initialState π)).bind fun r ↦
    (commitStackPure r.1.1.stackLog r.1.2 r.2).map fun t ↦ (r.1, t.2)

/-- **`afterRootDirect` is `afterRoot`.** -/
theorem afterRootDirect_eq (bytecode : List K) (π : Proof) :
    afterRootDirect bytecode π = afterRoot bytecode π := by
  show _ = runPure (announceSizesAndRoot bytecode) (initialState π)
  unfold announceSizesAndRoot afterRootDirect
  rw [runPure_bind, runPure_readSizes]
  cases readSizesPure bytecode (initialState π) with
  | none => rfl
  | some r =>
    obtain ⟨⟨layout, R⟩, s1⟩ := r
    show (commitStackPure layout.stackLog R s1).map (fun t ↦ ((layout, R), t.2)) =
      runPure (commitStack layout.stackLog R >>= fun _ ↦ pure (layout, R)) s1
    rw [runPure_bind, runPure_commitStack]
    cases commitStackPure layout.stackLog R s1 <;> rfl

theorem afterRootDirect_eq_afterRoot : afterRootDirect = afterRoot := by
  funext bytecode π
  exact afterRootDirect_eq bytecode π

/-! ## The lighter layout -/

/-- The fields of a layout the extractor reads. -/
structure LayoutLite where
  logMemory : ℕ
  logBytecode : ℕ
  placements : List (Option Placement)
  stackLog : ℕ
  tableLogHeights : List ℕ

/-- A layout's fields the extractor reads. -/
@[expose] def layoutLite (layout : Layout) : LayoutLite :=
  ⟨layout.logMemory, layout.logBytecode, layout.placements, layout.stackLog,
    layout.tableLogHeights⟩

/-- `buildLayout`, only the fields the extractor reads: no bus blocks, no copy of the bytecode. -/
@[expose] def buildLayoutLite (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) :
    Option LayoutLite :=
  match log2Strict bytecode.length with
  | none => none
  | some logLength =>
    if busBits ≤ logLength ∧ 16 ≤ logMemory ∧ logMemory ≤ 32 ∧
        tableRows.all (· ≤ 2 ^ 32) ∧ logLength - busBits ≤ 32 ∧
        tableRows.length = tables.length then
      let logBytecode := logLength - busBits
      let tableLogHeights := List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
        tableLogFloors
      let placed := placementsOf (columnKappas logMemory logBytecode tableLogHeights)
      some ⟨logMemory, logBytecode, placed.1, placed.2, tableLogHeights⟩
    else none

/-- **`buildLayoutLite` is `buildLayout`'s fields the extractor reads.** -/
theorem buildLayoutLite_eq (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) :
    buildLayoutLite bytecode logMemory tableRows =
      (buildLayout bytecode logMemory tableRows).map layoutLite := by
  unfold buildLayoutLite buildLayout
  cases log2Strict bytecode.length with
  | none => rfl
  | some logLength =>
    dsimp only
    split_ifs <;> rfl

/-- An `afterRoot` result with its layout cut to the fields the extractor reads. -/
@[expose] def liteResult (r : (Layout × ℕ) × ProgState) : (LayoutLite × ℕ) × ProgState :=
  ((layoutLite r.1.1, r.1.2), r.2)

/-- `readSizesPure` with the lighter layout. -/
@[expose] def readSizesLite (bytecode : List K) (s : ProgState) :
    Option ((LayoutLite × ℕ) × ProgState) :=
  (readPure (2 + tables.length) s).bind fun r ↦
    if (r.1.all fun value ↦ value.limb 1 = 0 ∧ value.limb 2 = 0) then
      let logMemory := kToNat ((r.1.headD 0).limb 0)
      let tableRows := ((r.1.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)
      let logInverseRate := kToNat ((r.1.getLastD 0).limb 0)
      if 1 ≤ logInverseRate ∧ logInverseRate ≤ 4 then
        (buildLayoutLite bytecode logMemory tableRows).bind fun layout ↦
          if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
            some ((layout, logInverseRate), r.2)
          else none
      else none
    else none

theorem bind_map_layoutLite (o : Option Layout) (R : ℕ) (st : ProgState) :
    (o.map layoutLite).bind (fun layout ↦
        if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
          some ((layout, R), st)
        else none) =
      Option.map liteResult (o.bind fun layout ↦
        if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
          some ((layout, R), st)
        else none) := by
  cases o with
  | none => rfl
  | some layout =>
    show (if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
        some ((layoutLite layout, R), st) else none) =
      Option.map liteResult (if Whir.minLogStack ≤ layout.stackLog ∧
        layout.stackLog ≤ Whir.maxLogStack then some ((layout, R), st) else none)
    split_ifs <;> rfl

theorem readSizesLite_eq (bytecode : List K) (s : ProgState) :
    readSizesLite bytecode s = (readSizesPure bytecode s).map liteResult := by
  unfold readSizesLite readSizesPure
  cases readPure (2 + tables.length) s with
  | none => rfl
  | some r =>
    simp only [Option.bind_some]
    split_ifs <;>
      first
      | (rw [buildLayoutLite_eq]; exact bind_map_layoutLite _ _ _)
      | rfl

/-- `afterRootDirect` with the lighter layout. -/
@[expose] def afterRootLite (bytecode : List K) (π : Proof) :
    Option ((LayoutLite × ℕ) × ProgState) :=
  (readSizesLite bytecode (initialState π)).bind fun r ↦
    (commitStackPure r.1.1.stackLog r.1.2 r.2).map fun t ↦ (r.1, t.2)

/-- **`afterRootLite` is `afterRoot`, its layout cut to the fields the extractor reads.** -/
theorem afterRootLite_eq (bytecode : List K) (π : Proof) :
    afterRootLite bytecode π = (afterRoot bytecode π).map liteResult := by
  rw [← afterRootDirect_eq]
  unfold afterRootLite afterRootDirect
  rw [readSizesLite_eq]
  cases readSizesPure bytecode (initialState π) with
  | none => rfl
  | some r =>
    show Option.map _ (commitStackPure r.1.1.stackLog r.1.2 r.2) =
      Option.map liteResult (Option.map _ (commitStackPure r.1.1.stackLog r.1.2 r.2))
    cases commitStackPure r.1.1.stackLog r.1.2 r.2 <;> rfl

end

end LeanVM.Extraction.Fast
