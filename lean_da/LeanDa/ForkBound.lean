import LeanDa.AdvX

/-!
# The collision term of Wagner's forking reduction, bounded

Benedikt Wagner's forking reduction (`forkCollisionReduction`) runs the committed-soundness
adversary twice by the replay fork and, when the two runs extract different vectors committing to
one root, opens both at a position where they differ; `forkCollExpH` is the probability that the
two openings' climbs collide under the hash of a uniformly random table `h`. With `H` left as
queries (`forkX`, `Z₂`), the experiment for `h` is this computation answered by `h`
(`forkCollExpH_le_col`): the fork commutes with answering `H` by `h` (`contextFork_collapse`), so
both runs see the same `h`. The fork makes at most twice the queries of one run
(`isQueryBoundP_contextFork`), each run at most `Q + 1` for the adversary and `322 · nPad r + 1`
for the commitment its win checks, and the openings and climbs at most `644 · nPad r + 4 d + 6`
more (`d = 7 + logPad r`). So the term is at most `(N + 2)² / 2^256` for
`N = 2 Q + 1288 · nPad r + 4 d + 10` (`forkColl_le`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA: it bounds his
forking collision term.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.Duplex LeanDa.Fork PFunctor PqDas
open PqDas.CommittedSoundness
open scoped ENNReal

namespace LeanDa

section Fork

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × Challenges) (Fin (r * 128) → Cell) Crs Proof)
  (A : CodeBindingAdvB r Crs Proof)

/-- Wagner's reduction to committed soundness (`csReduction`) with `H` as queries. -/
noncomputable def csX (ckVC : Unit) : OracleComp (WSpec + XS) (Common.DigestBytes × (Fin (r * 128) → Cell)) := do
  let crs ← liftL (liftM ps.setup : OracleComp WSpec Crs)
  let out ← advX r ps A (ckVC, crs)
  let l ← liftL (HasQuery.query (spec := (Common.DigestBytes →ₒ Challenges)) (m := OracleComp WSpec) out.1.1)
  pure (out.1.1, ext crs (ckVC, out.1.1, l) out.1.2)

theorem csReduction_eq (h : HTab) (ckVC : Unit) :
    csReduction (argH r ps (Hh h)) ext (advH r ps A h) ckVC = simulateQ (col h) (csX r ps ext A ckVC) := by
  simp only [csX, simulateQ_bind, simulateQ_col_liftL, ← advH_eq]
  rfl

/-- The wrapped adversary of the fork (`wrappedAdv`) with `H` as queries. -/
noncomputable def wrX : OracleComp (WSpec + XS) (Common.DigestBytes × (Fin (r * 128) → Cell) × Challenges) := do
  let out ← csX r ps ext A ()
  let l ← liftL (HasQuery.query (spec := (Common.DigestBytes →ₒ Challenges)) (m := OracleComp WSpec) out.1)
  pure (out.1, out.2, l)

theorem wrappedAdv_eq (h : HTab) :
    wrappedAdv (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) () =
      simulateQ (col h) (wrX r ps ext A) := by
  simp only [wrX, simulateQ_bind, simulateQ_col_liftL, ← csReduction_eq]
  rfl

/-- The win of a run of the fork (`winOn`) with `H` as queries. -/
noncomputable def winX (out : Common.DigestBytes × (Fin (r * 128) → Cell) × Challenges) :
    OracleComp (wrappedSpec Challenges + XS) Bool := do
  let root ← commitCellsM hS out.2.1
  pure (decide (out.2.1 ∉ (code r).code) && (checker r).check out.2.2 out.2.1 && decide (root = out.1))

theorem winX_eval (h : HTab) (out : Common.DigestBytes × (Fin (r * 128) → Cell) × Challenges) :
    simulateQ (col h) (winX r out) = pure (winOn (code r) (merkleVC r (Hh h)) (checker r) () out) := by
  rw [winX, simulateQ_bind, commitCellsM_eval (fun x ↦ simulateQ (col h) x) (fun a ↦ rfl)
    (fun x f ↦ simulateQ_bind _ x f) hS (Hh h) (simulateQ_col_hS h), pure_bind]
  rfl

/-- **A run of the fork** (`runTrace`) with `H` as queries. -/
noncomputable def mainX : OracleComp (wrappedSpec Challenges + XS) (Trace Cell (r * 128) Common.DigestBytes Challenges) := do
  let p ← (simulateQ (extImpl (unifForward Common.DigestBytes Challenges + roImpl Common.DigestBytes Challenges))
    (wrX r ps ext A)).run (∅, [])
  let w ← winX r p.1
  pure { com := p.1.1, vec := p.1.2.1, chal := p.1.2.2, roCache := p.2.1, queryLog := p.2.2, win := w }

theorem runTrace_eq (h : HTab) :
    runTrace (code r) (merkleVC r (Hh h)) (checker r)
      (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) () = simulateQ (col h) (mainX r ps ext A) := by
  rw [runTrace, wrappedAdv_eq, run_simulateQ_col_ext, mainX, simulateQ_bind]
  congr 1
  funext p
  rw [simulateQ_bind, winX_eval, pure_bind]
  rfl

/-- The fork's query budgets, with no budget for `XS`. -/
def qbX (Q : ℕ) : ((ℕ ⊕ Unit) ⊕ HDom) → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr ()) => Q + 1
  | .inr _ => 0

/-- **The fork and its two vectors** (`forkVecPair`) with `H` as queries. -/
noncomputable def forkX (Q : ℕ) :
    OracleComp (wrappedSpec Challenges + XS) ((Fin (r * 128) → Cell) × (Fin (r * 128) → Cell)) :=
  contextFork (mainX r ps ext A) (qbX Q) (.inl (.inr ())) (forkPoint (Q + 1)) >>= fun o ↦
    match o with
    | some (x₁, x₂) => pure (x₁.vec, x₂.vec)
    | none => pure (fun _ ↦ default, fun _ ↦ default)

theorem forkVecPair_eq (h : HTab) (Q : ℕ) :
    forkVecPair (code r) (merkleVC r (Hh h)) (checker r)
      (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) (Q + 1) () =
      simulateQ (col h) (forkX r ps ext A Q) := by
  rw [forkVecPair, runTrace_eq, forkX, simulateQ_bind]
  change contextFork (simulateQ (col h) (mainX r ps ext A)) (fun i ↦ qbX Q (.inl i)) (Sum.inr ())
    (forkPoint (Q + 1)) >>= _ = _
  erw [contextFork_collapse h (mainX r ps ext A) (qbX Q) (Sum.inr ()) (forkPoint (Q + 1))]
  congr 1
  funext o
  rcases o with _ | ⟨x₁, x₂⟩ <;> rfl

/-- The fork's oracles answered by uniform sampling. -/
noncomputable abbrev forkI : QueryImpl (wrappedSpec Challenges) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    uniformSampleImpl (spec := ((Unit →ₒ Challenges) : OracleSpec Unit))

theorem forkCollisionReduction_eq (h : HTab) (Q : ℕ) :
    forkCollisionReduction (code r) (merkleVC r (Hh h)) (checker r)
      (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) (Q + 1) () =
      simulateQ (col h) (simulateQ (extI forkI) (forkX r ps ext A Q)) := by
  rw [forkCollisionReduction, forkVecPair_eq, simulateQ_col_extI]

end Fork

/-! ## The openings of two different vectors and their collision -/

theorem findCollision_self (H : List UInt8 → Common.DigestBytes) (l : List (List UInt8)) :
    findCollision H l l = ([], []) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [findCollision, ih]

/-- The two climbs Wagner's forking reduction compares, from two vectors. -/
def colPair (r : ℕ) [NeZero r] (H : List UInt8 → Common.DigestBytes)
    (vv : (Fin (r * 128) → Cell) × (Fin (r * 128) → Cell)) : List UInt8 × List UInt8 :=
  if hv : vv.1 = vv.2 then ([], [])
  else
    let i := Fin.find (fun j ↦ vv.1 j ≠ vv.2 j) (Function.ne_iff.mp hv)
    openingsCollision H r i (vv.1 i) (openCell H vv.1 i) (vv.2 i) (openCell H vv.2 i)

/-- The same with `H` as queries. -/
def colPairX (r : ℕ) [NeZero r] (vv : (Fin (r * 128) → Cell) × (Fin (r * 128) → Cell)) :
    OracleComp (unifSpec + XS) (List UInt8 × List UInt8) :=
  if hv : vv.1 = vv.2 then pure ([], [])
  else
    let i := Fin.find (fun j ↦ vv.1 j ≠ vv.2 j) (Function.ne_iff.mp hv)
    do
      let τ ← openCellM hS vv.1 i
      let τ' ← openCellM hS vv.2 i
      let l₁ ← hashInputsM hS (colIndex i) (cellBytes (vv.1 i)) (τ.path.take (7 + logPad r))
        τ.rowRoot
      let l₂ ← hashInputsM hS (colIndex i) (cellBytes (vv.2 i)) (τ'.path.take (7 + logPad r))
        τ'.rowRoot
      findCollisionM hS l₁ (l₂.take (9 + logPad r))

theorem length_hashInputs (H : List UInt8 → Common.DigestBytes) (path : List Common.DigestBytes) :
    ∀ (idx : ℕ) (a : List UInt8) (rr : Common.DigestBytes), (hashInputs H idx a path rr).length = path.length + 2 := by
  induction path with
  | nil => intro idx a rr; rfl
  | cons s rest ih => intro idx a rr; simp [hashInputs, ih]

theorem mem_hashInputs (H : List UInt8 → Common.DigestBytes) (path : List Common.DigestBytes) :
    ∀ (idx : ℕ) (a : List UInt8) (rr : Common.DigestBytes) (x : List UInt8), x ∈ hashInputs H idx a path rr →
      x = a ∨ ∃ d₁ d₂, x = pairBytes d₁ d₂ := by
  induction path with
  | nil =>
    intro idx a rr x hx
    simp only [hashInputs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨_, _, rfl⟩
  | cons s rest ih =>
    intro idx a rr x hx
    simp only [hashInputs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · rcases ih _ _ rr x hx with rfl | h
      · split <;> exact Or.inr ⟨_, _, rfl⟩
      · exact Or.inr h

theorem shortP_of_mem_hashInputs (H : List UInt8 → Common.DigestBytes) (path : List Common.DigestBytes) (idx : ℕ)
    (x : Cell) (rr : Common.DigestBytes) (y : List UInt8) (hy : y ∈ hashInputs H idx (cellBytes x) path rr) :
    shortP y := by
  rcases mem_hashInputs H path idx _ rr y hy with rfl | ⟨d₁, d₂, rfl⟩
  · simp [shortP, length_cellBytes]
  · simp [shortP, length_pairBytes]

/-- **The climbs' colliding inputs are short.** -/
theorem shortP_colPair (r : ℕ) [NeZero r] (H : List UInt8 → Common.DigestBytes)
    (vv : (Fin (r * 128) → Cell) × (Fin (r * 128) → Cell))
    (hne : (colPair r H vv).1 ≠ (colPair r H vv).2) :
    shortP (colPair r H vv).1 ∧ shortP (colPair r H vv).2 := by
  unfold colPair at hne ⊢
  split at hne
  · exact absurd rfl hne
  · next hv =>
    simp only [hv, ↓reduceDIte] at hne ⊢
    obtain ⟨h1, h2⟩ := findCollision_mem H _ _ hne
    exact ⟨shortP_of_mem_hashInputs H _ _ _ _ _ h1, shortP_of_mem_hashInputs H _ _ _ _ _ h2⟩

theorem colPairX_eval (r : ℕ) [NeZero r] (h : HTab)
    (vv : (Fin (r * 128) → Cell) × (Fin (r * 128) → Cell)) :
    simulateQ (col h) (colPairX r vv) = pure (colPair r (Hh h) vv) := by
  have hp : ∀ {α} (a : α), simulateQ (col (Ψ := unifSpec) h) (pure a) = pure a := fun _ ↦ rfl
  have hb : ∀ {α β} (x : OracleComp (unifSpec + XS) α) (f : α → OracleComp (unifSpec + XS) β),
      simulateQ (col h) (x >>= f) = simulateQ (col h) x >>= fun a ↦ simulateQ (col h) (f a) :=
    fun x f ↦ simulateQ_bind _ x f
  unfold colPairX colPair
  split
  · rfl
  · simp only [hb, openCellM_eval (fun x ↦ simulateQ (col h) x) hp hb hS (Hh h) (simulateQ_col_hS h),
      hashInputsM_eval (fun x ↦ simulateQ (col h) x) hp hb hS (Hh h) (simulateQ_col_hS h),
      findCollisionM_eval (fun x ↦ simulateQ (col h) x) hp hb hS (Hh h) (simulateQ_col_hS h),
      pure_bind]
    congr 1
    have e1 : ∀ (c : Fin (r * 128) → Cell) (i : Fin (r * 128)),
        (openCell (Hh h) c i).path.take (7 + logPad r) = (openCell (Hh h) c i).path := fun c i ↦
      List.take_of_length_le (by simp [openCell, length_merklePath])
    simp only [openingsCollision, e1]
    rw [List.take_of_length_le (by rw [length_hashInputs]; simp [openCell, length_merklePath]; omega)]

section Fork2

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × Challenges) (Fin (r * 128) → Cell) Crs Proof)
  (A : CodeBindingAdvB r Crs Proof)

/-- **Wagner's forking collision experiment for the table `h`, as a function of the two vectors.** -/
theorem forkCollExpH_eq [NeZero r] (h : HTab) (Q : ℕ) :
    forkCollExpH r ps ext A Q h = (fun vv ↦ decide ((colPair r (Hh h) vv).1 ≠ (colPair r (Hh h) vv).2) &&
      decide (Hh h (colPair r (Hh h) vv).1 = Hh h (colPair r (Hh h) vv).2)) <$>
        forkCollisionReduction (code r) (merkleVC r (Hh h)) (checker r)
          (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) (Q + 1) () := by
  simp only [forkCollExpH, hashCollisionExp, merkleCollider,
    VectorCommitment.CollisionAdv.toPosBindingAdv, bind_assoc, map_eq_bind_pure_comp]
  congr 1
  funext vv
  obtain ⟨v, v'⟩ := vv
  simp only [colPair]
  by_cases hv : v = v'
  · subst hv
    simp [merkleVC, openingsCollision, findCollision_self]
  · simp [merkleVC, hv]

end Fork2


/-! ## Queries of `H` -/

section Weight

variable {ι κ ιs : Type} {Ψ : OracleSpec ι} {spec : OracleSpec ιs} {σ α : Type}

theorem isWeightBound_extImpl (impl : QueryImpl spec (StateT σ (OracleComp Ψ)))
    (t : (spec + XS).Domain) (s : σ) :
    QueryCostAtMost (((extImpl impl) t).run s) xCalls (xCalls t) := by
  rcases t with t | x
  · exact isWeightBound_liftL _
  · exact isWeightBound_map _ (isWeightBound_query (spec := Ψ + XS) xCalls (.inr x))

theorem isWeightBound_extI (I : QueryImpl spec (OracleComp Ψ)) (t : (spec + XS).Domain) :
    QueryCostAtMost ((extI I) t) xCalls (xCalls t) := by
  rcases t with t | x
  · exact isWeightBound_liftL _
  · exact isWeightBound_query (spec := Ψ + XS) xCalls (.inr x)

theorem isWeightBound_iff_isQueryBoundP {oa : OracleComp (Ψ + XS) α} {N : ℕ} :
    QueryCostAtMost oa xCalls N ↔ IsQueryBoundP oa (fun j ↦ j.isRight = true) N :=
  isQueryBound_congr (fun t b ↦ by rcases t with t | x <;> simp [xCalls]; omega)
    (fun t b ↦ by rcases t with t | x <;> simp [xCalls])

end Weight

section Fork3

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × Challenges) (Fin (r * 128) → Cell) Crs Proof)
  (A : CodeBindingAdvB r Crs Proof)

/-- The hash calls of an honest opening over `H` as queries. -/
abbrev openCalls (r : ℕ) : ℕ := 322 * nPad r

/-- The hash calls of the commitment over `H` as queries. -/
abbrev commitCalls (r : ℕ) : ℕ := 322 * nPad r + 1

set_option maxRecDepth 4000 in
theorem isWeightBound_commitCellsM_hS {ι : Type} {Ψ : OracleSpec ι} (c : Fin (r * 128) → Cell) :
    QueryCostAtMost (commitCellsM (hS (Ψ := Ψ)) c) xCalls (commitCalls r) := by
  have := isWeightBound_commitCellsM (hS (Ψ := Ψ)) xCalls 1 1 1
    (fun a b ↦ isWeightBound_hS (Ψ := Ψ) (pairBytes a b))
    (fun x ↦ isWeightBound_hS (Ψ := Ψ) (cellBytes x))
    (fun _ _ ↦ isWeightBound_hS (Ψ := Ψ) _) c
  exact this.mono (le_of_eq (by ring))

set_option maxRecDepth 4000 in
theorem isWeightBound_openCellM_hS {ι : Type} {Ψ : OracleSpec ι} (c : Fin (r * 128) → Cell)
    (i : Fin (r * 128)) : QueryCostAtMost (openCellM (hS (Ψ := Ψ)) c i) xCalls (openCalls r) := by
  have := isWeightBound_openCellM (hS (Ψ := Ψ)) xCalls 1 1 1
    (fun a b ↦ isWeightBound_hS (Ψ := Ψ) (pairBytes a b))
    (fun x ↦ isWeightBound_hS (Ψ := Ψ) (cellBytes x))
    (fun _ _ ↦ isWeightBound_hS (Ψ := Ψ) _) c i
  exact this.mono (le_of_eq (by ring))

theorem isWeightBound_winX (out : Common.DigestBytes × (Fin (r * 128) → Cell) × Challenges) :
    QueryCostAtMost (winX r out) xCalls (commitCalls r) := by
  have := (isWeightBound_commitCellsM_hS r (Ψ := wrappedSpec Challenges) out.2.1).bind
    fun root ↦ isWeightBound_pure (spec := wrappedSpec Challenges + XS)
      (decide (out.2.1 ∉ (code r).code) && (checker r).check out.2.2 out.2.1 &&
        decide (root = out.1)) xCalls 0
  exact this

theorem isWeightBound_mainX (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    QueryCostAtMost (mainX r ps ext A) xCalls (Q + 1 + commitCalls r) := by
  have hcs : QueryCostAtMost (csX r ps ext A ()) xCalls (Q + 1) :=
    ((isWeightBound_liftL _).bind fun _ ↦ (isWeightBound_advX r ps A Q hQ _).bind fun _ ↦
      (isWeightBound_liftL _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (by omega)
  have hwr : QueryCostAtMost (wrX r ps ext A) xCalls (Q + 1) :=
    (hcs.bind fun _ ↦ (isWeightBound_liftL _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono
      (by omega)
  have hrun := isWeightBound_run_simulateQ
    (extImpl (Ψ := wrappedSpec Challenges) (unifForward Common.DigestBytes Challenges + roImpl Common.DigestBytes Challenges))
    xCalls xCalls (isWeightBound_extImpl _) hwr
    (((∅ : (Common.DigestBytes →ₒ Challenges).QueryCache), ([] : List Common.DigestBytes)) : SimState Common.DigestBytes Challenges)
  exact (hrun.bind fun p ↦ ((isWeightBound_winX r p.1).bind fun w ↦
    isWeightBound_pure _ _ 0)).mono le_rfl


theorem isWeightBound_colPairX [NeZero r] (vv : (Fin (r * 128) → Cell) × (Fin (r * 128) → Cell)) :
    QueryCostAtMost (colPairX r vv) xCalls
      (2 * openCalls r + 2 * (7 + logPad r + 1) + 2 * (9 + logPad r)) := by
  unfold colPairX
  split
  · exact isWeightBound_pure _ _ _
  · have hO : ∀ c i, QueryCostAtMost (openCellM (hS (Ψ := unifSpec)) c i) xCalls (openCalls r) :=
      fun c i ↦ isWeightBound_openCellM_hS r c i
    have hI : ∀ idx a (path : List Common.DigestBytes) rr, QueryCostAtMost
        (hashInputsM hS idx a (path.take (7 + logPad r)) rr) xCalls (7 + logPad r + 1) :=
      fun idx a path rr ↦ (isWeightBound_hashInputsM (hS (Ψ := unifSpec)) xCalls
        (fun _ ↦ isWeightBound_hS _) _ idx a rr).mono (by simp only [List.length_take]; omega)
    have hF : ∀ l₁ (l₂ : List (List UInt8)), QueryCostAtMost (findCollisionM hS l₁ (l₂.take (9 + logPad r)))
        xCalls (2 * (9 + logPad r)) :=
      fun l₁ l₂ ↦ (isWeightBound_findCollisionM (hS (Ψ := unifSpec)) xCalls
        (fun _ ↦ isWeightBound_hS _) l₁ _).mono (by simp only [List.length_take]; omega)
    exact ((hO _ _).bind fun _ ↦ (hO _ _).bind fun _ ↦ (hI _ _ _ _).bind fun _ ↦
      (hI _ _ _ _).bind fun _ ↦ hF _ _).mono (by omega)

/-- **The forking reduction's collision search with `H` as queries.** -/
noncomputable def forkZ [NeZero r] (Q : ℕ) :
    OracleComp (unifSpec + XS) (List UInt8 × List UInt8) :=
  simulateQ (extI forkI) (forkX r ps ext A Q) >>= colPairX r

/-- Its hash calls. -/
abbrev forkCalls (r Q : ℕ) : ℕ :=
  2 * (Q + 1 + commitCalls r) + (2 * openCalls r + 2 * (7 + logPad r + 1) + 2 * (9 + logPad r))

theorem isWeightBound_forkZ [NeZero r] (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    QueryCostAtMost (forkZ r ps ext A Q) xCalls (forkCalls r Q) := by
  have hm := isWeightBound_iff_isQueryBoundP.mp (isWeightBound_mainX r ps ext A Q hQ)
  have hf := isWeightBound_iff_isQueryBoundP.mpr
    (isQueryBoundP_contextFork _ (mainX r ps ext A) (qbX Q) (.inl (.inr ())) (forkPoint (Q + 1)) _ hm)
  have hX : QueryCostAtMost (forkX r ps ext A Q) xCalls (2 * (Q + 1 + commitCalls r)) := by
    refine (hf.bind fun o ↦ (?_ : QueryCostAtMost _ xCalls 0)).mono (by omega)
    rcases o with _ | ⟨x₁, x₂⟩ <;> exact isWeightBound_pure _ _ _
  exact (isWeightBound_simulateQ _ xCalls xCalls (isWeightBound_extI forkI) hX).bind fun vv ↦
    isWeightBound_colPairX r vv

theorem prEvent_bind_mono' {α β : Type} (mx : ProbComp α) (f g : α → ProbComp β) (P : β → Prop)
    (h : ∀ x, Pr{let y ← f x}[P y] ≤ Pr{let y ← g x}[P y]) :
    Pr{let y ← mx >>= f}[P y] ≤ Pr{let y ← mx >>= g}[P y] := by
  simpa using Common.prEvent_bind_le_add_const mx f g P P 0 (fun x ↦ by simpa using h x)

/-- **Wagner's forking collision term is a birthday bound**: at most `(N + 2)² / 2^256` for the
`N = forkCalls r Q` hash calls of the forked search, for an RPM adversary of `Q` permutation
calls. -/
theorem forkColl_le [NeZero r] (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= forkCollExpH r ps ext A Q}[b = true] ≤
      ((forkCalls r Q + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  have hpt : ∀ h : HTab, Pr{let b ← forkCollExpH r ps ext A Q h}[b = true] ≤
      Pr{let b ← simulateQ (col h) (forkZ r ps ext A Q >>= finalCheck)}[b = true] := by
    intro h
    have e : ∀ vv, simulateQ (col h) (colPairX r vv >>= finalCheck) =
        pure (decide (shortP (colPair r (Hh h) vv).1 ∧ shortP (colPair r (Hh h) vv).2) &&
          (decide ((colPair r (Hh h) vv).1 ≠ (colPair r (Hh h) vv).2) &&
            decide (Hh h (colPair r (Hh h) vv).1 = Hh h (colPair r (Hh h) vv).2))) := fun vv ↦ by
      rw [simulateQ_bind, colPairX_eval, pure_bind, simulateQ_col_finalCheck]
    have e2 : simulateQ (col h) (forkZ r ps ext A Q >>= finalCheck) =
        simulateQ (col h) (simulateQ (extI forkI) (forkX r ps ext A Q)) >>= fun vv ↦
          simulateQ (col h) (colPairX r vv >>= finalCheck) := by
      rw [forkZ, bind_assoc, simulateQ_bind]
    rw [e2, forkCollExpH_eq, forkCollisionReduction_eq, prEvent_map]
    simp only [e]
    rw [bind_pure_comp, prEvent_map]
    refine prEvent_mono _ _ _ fun vv hv ↦ ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
    exact ⟨shortP_colPair r (Hh h) vv hv.1, hv⟩
  exact (prEvent_bind_mono' _ _ _ _ hpt).trans
    (prob_collision_le _ _ (isWeightBound_forkZ r ps ext A Q hQ))

end Fork3

end LeanDa
