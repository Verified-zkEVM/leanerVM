/-
  LeanVM.E2E.Complete.CapsRange

  The deferring verifier queries every committed tree below its leaf count: its phases before
  WHIR neither commit nor query, the stack is commitment `0` at the height WHIR's first level
  samples its positions at, and each WHIR level commits the next level's tree at the height that
  level samples at.
-/

module

public import LeanVM.E2E.Complete.Caps
public import LeanVM.E2E.Complete.Deferred

/-!
# The deferring verifier's queries are in range

`QRange hts p` (`Caps.lean`): every query of `p` opens its tree below the tree's leaf count.
Here `qRange_deferredProgram`: the deferring verifier, for every claims `c`, from no commitment.

* `NoCQ p`: `p` neither commits nor queries; the phases before WHIR are such programs
  (`noCQ_readSizes`, `noCQ_verifyBusBalance`, `noCQ_tablePhase`, `noCQ_publicInputPhase`,
  `noCQ_verifyFlock`, `noCQ_ringSwitch`, after `LeanVM.Protocol.EndToEnd.Sound.Moves`), and
  `QRange` passes through them (`QRange.bind_noCQ`), keeping what they return
  (`QRange.bind_noCQ_allRet`);
* the stack's commitment (`commitStack`) has the height `logN - fold + rate` of WHIR's first
  level, and level `i` samples its positions below `2^(logN - folds + rate)`
  (`allRet_sampleQueries`), its folds counted by `allRet_foldRounds`; the next level's commitment
  has the height the next level samples at (`qRange_whirLevels`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {α β : Type}

/-! ## Programs without commitments or queries -/

/-- **`p` neither commits nor queries.** -/
def NoCQ : Prog α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, NoCQ (k x)
  | .sample k => ∀ x, NoCQ (k x)
  | .grind _ k => NoCQ k
  | .commit _ _ _ => False
  | .query _ _ _ => False

namespace NoCQ

/-- **Sequencing.** -/
theorem bind {p : Prog α} {f : α → Prog β} (hp : NoCQ p) (hf : ∀ a, NoCQ (f a)) :
    NoCQ (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | grind b k ih => exact ih hp
  | commit ht w k ih => exact hp.elim
  | query i ps k ih => exact hp.elim

/-- Sequencing in `do` notation. -/
theorem seq {p : Prog α} {f : α → Prog β} (hp : NoCQ p) (hf : ∀ a, NoCQ (f a)) :
    NoCQ (p >>= f) :=
  bind hp hf

/-- `pure`. -/
theorem pure (a : α) : NoCQ (Pure.pure a : Prog α) := trivial

/-- A read. -/
theorem readE : NoCQ Prog.readE := fun _ ↦ trivial

/-- A sample. -/
theorem sampleE : NoCQ Prog.sampleE := fun _ ↦ trivial

/-- `n` reads. -/
theorem readN : ∀ n, NoCQ (Prog.readN n)
  | 0 => trivial
  | n + 1 => seq readE fun _ ↦ seq (readN n) fun _ ↦ trivial

/-- `n` samples. -/
theorem sampleN : ∀ n, NoCQ (Prog.sampleN n)
  | 0 => trivial
  | n + 1 => seq sampleE fun _ ↦ seq (sampleN n) fun _ ↦ trivial

/-- A check. -/
theorem require (q : Prop) [Decidable q] : NoCQ (Prog.require q) := by
  unfold Prog.require
  split <;> trivial

/-- A pure step that may fail. -/
theorem liftOption (o : Option α) : NoCQ (Verifier.liftOption o) := by
  cases o <;> trivial

/-- A conditional. -/
theorem ite {q : Prop} [Decidable q] {p p' : Prog α} (hp : q → NoCQ p) (hp' : ¬ q → NoCQ p') :
    NoCQ (if q then p else p') := by
  split
  · exact hp ‹_›
  · exact hp' ‹_›

end NoCQ

/-! ## Queries in range through sequencing -/

/-- **`QRange` through a program without commitments or queries**, keeping what it returns. -/
theorem QRange.bind_noCQ_allRet {hts : List ℕ} {Q : α → Prop} {f : α → Prog β} {p : Prog α}
    (hp : NoCQ p) (hq : AllRet Q p) (hf : ∀ a, Q a → QRange hts (f a)) :
    QRange hts (p.bind f) := by
  induction p with
  | ret a => exact hf a hq
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x) (hq x)
  | sample k ih => exact fun x ↦ ih x (hp x) (hq x)
  | grind b k ih => exact ih hp hq
  | commit ht w k ih => exact hp.elim
  | query i ps k ih => exact hp.elim

/-- **`QRange` through a program without commitments or queries.** -/
theorem QRange.bind_noCQ {hts : List ℕ} {p : Prog α} {f : α → Prog β} (hp : NoCQ p)
    (hf : ∀ a, QRange hts (f a)) : QRange hts (p.bind f) :=
  QRange.bind_noCQ_allRet hp (allRet_true p) fun a _ ↦ hf a

/-- **`QRange` before a continuation without queries**: whatever the continuation's heights. -/
theorem QRange.bind_any {f : α → Prog β} (hf : ∀ a hts, QRange hts (f a)) {p : Prog α}
    {hts : List ℕ} (hp : QRange hts p) : QRange hts (p.bind f) := by
  induction p generalizing hts with
  | ret a => exact hf a hts
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | grind b k ih => exact ih hp
  | commit ht w k ih => exact ih hp
  | query i ps k ih => exact ⟨hp.1, fun rows ↦ ih rows (hp.2 rows)⟩

section Phases

attribute [local irreducible] NoCQ

/-- A round polynomial is reads. -/
theorem noCQ_sumcheckRoundPoly (count : ℕ) (claim : E) (eq : Option E) :
    NoCQ (sumcheckRoundPoly count claim eq) := by
  cases eq with
  | none =>
    exact NoCQ.seq NoCQ.readE fun _ ↦ NoCQ.seq (NoCQ.readN _) fun _ ↦ NoCQ.pure _
  | some r => exact NoCQ.seq (NoCQ.readN _) fun _ ↦ NoCQ.pure _

/-- A sumcheck is reads and samples. -/
theorem noCQ_sumcheck (count : ℕ) : ∀ (claim : E) (eqs : List (Option E)),
    NoCQ (sumcheck claim count eqs)
  | _, [] => NoCQ.pure _
  | claim, e :: es =>
    NoCQ.seq (noCQ_sumcheckRoundPoly count claim e) fun _ ↦
      NoCQ.seq NoCQ.sampleE fun _ ↦
        NoCQ.seq (noCQ_sumcheck count _ es) fun r ↦ by
          obtain ⟨point, final⟩ := r
          exact NoCQ.pure _

/-- One GKR step is reads and samples. -/
theorem noCQ_gkrStep (step : ℕ) (s : GkrState) :
    NoCQ (gkrStep step s) := by
  refine NoCQ.seq NoCQ.sampleE fun _ ↦ NoCQ.seq (noCQ_sumcheck _ _ _) fun r ↦ ?_
  obtain ⟨x, claim⟩ := r
  exact NoCQ.seq (NoCQ.readN _) fun _ ↦ NoCQ.seq (NoCQ.readN _) fun _ ↦
    NoCQ.seq (NoCQ.readN _) fun _ ↦ NoCQ.seq (NoCQ.require _) fun _ ↦
      NoCQ.seq (NoCQ.sampleN _) fun _ ↦ NoCQ.pure _

/-- The GKR walk is reads and samples. -/
theorem noCQ_gkrLayers : ∀ (n : ℕ) (s : GkrState),
    NoCQ (gkrLayers n s)
  | 0, _ => NoCQ.pure _
  | 1, s => NoCQ.seq (noCQ_gkrStep 1 s) fun t ↦ noCQ_gkrLayers 0 t
  | n + 2, s => by
    simp only [gkrLayers]
    split
    · exact NoCQ.seq (noCQ_gkrStep 1 s) fun t ↦ noCQ_gkrLayers (n + 1) t
    · exact NoCQ.seq (noCQ_gkrStep 2 s) fun t ↦ noCQ_gkrLayers n t

/-- The GKR grand products are reads and samples. -/
theorem noCQ_verifyGkrGrandProducts (depth : ℕ) :
    NoCQ (verifyGkrGrandProducts depth) :=
  NoCQ.seq NoCQ.readE fun _ ↦ NoCQ.seq NoCQ.readE fun _ ↦
    NoCQ.seq (noCQ_gkrLayers depth _) fun _ ↦ NoCQ.pure _

/-- The bus makes no prover move other than reads. -/
theorem noCQ_verifyBusBalance {ev : Evaluations} (hev : ∀ w p, NoCQ (ev.bytecode w p))
    (layout : Layout) : NoCQ (verifyBusBalance ev layout) := by
  refine NoCQ.seq (NoCQ.sampleN _) fun _ ↦ NoCQ.seq NoCQ.sampleE fun _ ↦
    NoCQ.seq (noCQ_verifyGkrGrandProducts _) fun r ↦ ?_
  obtain ⟨countRoot, point, treeValues⟩ := r
  exact NoCQ.seq (NoCQ.require _) fun _ ↦ NoCQ.seq (NoCQ.readN 3) fun _ ↦
    NoCQ.seq NoCQ.readE fun _ ↦ NoCQ.seq NoCQ.readE fun _ ↦
      NoCQ.seq (hev _ _) fun _ ↦ NoCQ.pure _

/-! ## The sizes, the table sumcheck and the public input -/

/-- The announced sizes are reads. -/
theorem noCQ_readSizes (bytecode : List K) :
    NoCQ (readSizes bytecode) :=
  NoCQ.seq (NoCQ.readN _) fun _ ↦ NoCQ.seq (NoCQ.require _) fun _ ↦
    NoCQ.seq (NoCQ.require _) fun _ ↦ NoCQ.seq (NoCQ.liftOption _) fun _ ↦
      NoCQ.seq (NoCQ.require _) fun _ ↦ NoCQ.pure _

/-- The tables' row evaluations are reads. -/
theorem noCQ_tableTerms (constraintPowers formPowers point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim),
      NoCQ
        (tableTerms constraintPowers formPowers point rows cursor final claims)
  | [], _, _, _ => NoCQ.pure _
  | (_, _, _, _) :: rest, _, _, _ =>
    NoCQ.seq (NoCQ.readN _) fun _ ↦
      noCQ_tableTerms constraintPowers formPowers point rest _ _ _

/-- The table sumcheck is reads and samples. -/
theorem noCQ_tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) :
    NoCQ
      (tableSumcheck heights busForms constraintPowers formPowers equalityPoint target) := by
  refine NoCQ.seq (noCQ_sumcheck _ _ _) fun r ↦ ?_
  obtain ⟨challenges, claim⟩ := r
  refine NoCQ.seq (noCQ_tableTerms _ _ _ _ 0 0 []) fun r ↦ ?_
  obtain ⟨final, claims⟩ := r
  exact NoCQ.seq (NoCQ.require _) fun _ ↦ NoCQ.pure _

/-- The table phase makes no prover move other than reads. -/
theorem noCQ_tablePhase (layout : Layout) (bus : BusResult) :
    NoCQ (tablePhase layout bus) :=
  NoCQ.seq NoCQ.sampleE fun _ ↦ NoCQ.seq (noCQ_tableSumcheck _ _ _ _ _ _) fun _ ↦
    NoCQ.pure _

/-- The public-input phase makes no prover move: one challenge. -/
theorem noCQ_publicInputPhase (layout : Layout) (publicInput : Digest) :
    NoCQ (publicInputPhase layout publicInput) :=
  NoCQ.seq NoCQ.sampleE fun _ ↦ NoCQ.pure _

/-! ## Flock and ring switching -/

/-- The Flock zerocheck is reads and samples. -/
theorem noCQ_verifyFlockZerocheck (logN : ℕ) :
    NoCQ (verifyFlockZerocheck logN) := by
  refine NoCQ.seq (NoCQ.sampleN _) fun _ ↦ NoCQ.seq (NoCQ.readN _) fun _ ↦
    NoCQ.seq NoCQ.sampleE fun _ ↦ NoCQ.seq (noCQ_sumcheck _ _ _) fun r ↦ ?_
  obtain ⟨chi, running⟩ := r
  exact NoCQ.seq NoCQ.readE fun _ ↦ NoCQ.seq NoCQ.readE fun _ ↦ NoCQ.pure _

/-- The Flock lincheck is reads and samples. -/
theorem noCQ_verifyFlockLincheck {ev : Evaluations}
    (hev : ∀ a z r c s, NoCQ (ev.matrices a z r c s)) (zc : ZerocheckResult) :
    NoCQ (verifyFlockLincheck ev zc) := by
  refine NoCQ.seq NoCQ.sampleE fun _ ↦ NoCQ.seq (noCQ_sumcheck _ _ _) fun r ↦ ?_
  obtain ⟨roundChallenges, rLc⟩ := r
  exact NoCQ.seq (NoCQ.readN _) fun _ ↦ NoCQ.seq (hev _ _ _ _ _) fun _ ↦
    NoCQ.seq (NoCQ.require _) fun _ ↦ NoCQ.pure _

/-- Flock makes no prover move other than reads. -/
theorem noCQ_verifyFlock {ev : Evaluations} (hev : ∀ a z r c s, NoCQ (ev.matrices a z r c s))
    (logN : ℕ) : NoCQ (verifyFlock ev logN) :=
  NoCQ.seq (noCQ_verifyFlockZerocheck logN) fun zc ↦ noCQ_verifyFlockLincheck hev zc

/-- Ring switching only samples. -/
theorem noCQ_ringSwitch (point s : List E) :
    NoCQ (ringSwitch point s) :=
  NoCQ.seq (NoCQ.sampleN _) fun _ ↦ NoCQ.pure _

/-! ## WHIR -/

/-- A WHIR level's fold rounds are reads and samples. -/
theorem noCQ_foldRounds : ∀ (n : ℕ) (s : WhirState) (levelFolds : List E),
    NoCQ (foldRounds n s levelFolds)
  | 0, _, _ => NoCQ.pure _
  | n + 1, _, _ =>
    NoCQ.seq NoCQ.sampleE fun _ ↦ NoCQ.seq (noCQ_sumcheckRoundPoly 3 _ none)
      fun _ ↦ noCQ_foldRounds n _ _

/-- The final WHIR level's tail rounds are reads and samples. -/
theorem noCQ_tailRounds : ∀ (n : ℕ) (target : E) (quad : List E),
    NoCQ (tailRounds n target quad)
  | 0, _, _ => NoCQ.pure _
  | n + 1, _, _ =>
    NoCQ.seq NoCQ.sampleE fun _ ↦ NoCQ.ite (fun _ ↦ NoCQ.pure _) fun _ ↦
      NoCQ.seq (noCQ_sumcheckRoundPoly 3 _ none) fun _ ↦
        NoCQ.seq (noCQ_tailRounds n _ _) fun r ↦ by
          obtain ⟨rest, target⟩ := r
          exact NoCQ.pure _

/-- The query sampling loop only samples. -/
theorem noCQ_sampleQueriesAux (depth : ℕ) : ∀ (fuel remaining : ℕ),
    NoCQ (sampleQueriesAux depth fuel remaining)
  | 0, _ => NoCQ.pure _
  | fuel + 1, _ =>
    NoCQ.ite (fun _ ↦ NoCQ.pure _) fun _ ↦ NoCQ.seq NoCQ.sampleE fun _ ↦
      NoCQ.seq (noCQ_sampleQueriesAux depth fuel _) fun _ ↦ NoCQ.pure _




end Phases

/-- A program without commitments or queries has its queries in range. -/
theorem QRange.of_noCQ {hts : List ℕ} {p : Prog α} (hp : NoCQ p) : QRange hts p := by
  have := QRange.bind_noCQ (hts := hts) (f := Prog.ret) hp fun _ ↦ trivial
  rwa [Prog.bind_ret] at this

/-- A proof of work neither commits nor queries. -/
theorem NoCQ.grindP (b : ℕ) : NoCQ (Prog.grindP b) := trivial

/-! ## WHIR -/

/-- A level's fold rounds add their count to the folds. -/
theorem allRet_foldRounds : ∀ (n : ℕ) (s : WhirState) (levelFolds : List E),
    AllRet (fun r : WhirState × List E ↦ r.1.folds.length = s.folds.length + n)
      (foldRounds n s levelFolds)
  | 0, _, _ => rfl
  | n + 1, s, levelFolds => by
    simp only [foldRounds, Prog.bind_eq]
    refine AllRet.bind (fun c _ ↦ ?_) _ (allRet_true _)
    refine AllRet.bind (fun q _ ↦ ?_) _ (allRet_true _)
    have := allRet_foldRounds n
      { s with target := polyEval s.quad c, quad := q, folds := s.folds ++ [c] }
      (levelFolds ++ [c])
    simp only [List.length_append, List.length_singleton] at this
    rwa [show s.folds.length + 1 + n = s.folds.length + (n + 1) by omega] at this

/-- The sampled positions are below `2^depth`. -/
theorem allRet_sampleQueriesAux (depth : ℕ) : ∀ (fuel remaining : ℕ),
    AllRet (fun qs : List ℕ ↦ ∀ q ∈ qs, q < 2 ^ depth) (sampleQueriesAux depth fuel remaining)
  | 0, _ => fun _ h ↦ by simp at h
  | fuel + 1, remaining => by
    simp only [sampleQueriesAux]
    split
    · exact fun _ h ↦ by simp at h
    · simp only [Prog.bind_eq]
      refine AllRet.bind (fun e _ ↦ ?_) _ (allRet_true _)
      refine AllRet.bind (fun rest hrest ↦ ?_) _ (allRet_sampleQueriesAux depth fuel _)
      intro q hq
      simp only [List.mem_append, List.mem_map, List.mem_range] at hq
      rcases hq with ⟨c, _, rfl⟩ | hq
      · exact Nat.mod_lt _ (Nat.two_pow_pos depth)
      · exact hrest q hq

/-- Gluing keeps the folds. -/
theorem glue_folds (lam : E) (s : WhirState) (pending : List (E × List E × (List E → E))) :
    (glue lam s pending).folds = s.folds := by
  unfold glue
  suffices h : ∀ (acc : WhirState × E), (pending.foldl (fun (acc : WhirState × E)
      (x : E × List E × (List E → E)) ↦
      ({ acc.1 with
          quad := List.zipWith (fun q i ↦ q + acc.2 * lam * i) acc.1.quad x.2.1
          target := acc.1.target + acc.2 * lam * x.1
          glued := acc.1.glued ++ [⟨acc.2 * lam, acc.1.folds.length, x.2.2⟩] }, acc.2 * lam))
      acc).1.folds = acc.1.folds from h (s, 1)
  induction pending with
  | nil => intro acc; rfl
  | cons x xs ih => intro acc; rw [List.foldl_cons, ih]

/-- **WHIR's levels query in range**: level `index` opens commitment `index` below its leaf
count, when that commitment has the height the level samples its positions at, and commits the
next level's tree at the height that level samples at. -/
theorem qRange_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (hts : List ℕ),
      hts.length = index + 1 →
      (∀ level ∈ levels.head?,
        hts[index]? = some (logN - (s.folds.length + level.fold) + level.logInvRate)) →
      QRange hts (whirLevels logN laneFolds evaluateBasis index levels s)
  | [], _, _, _, _, _ => trivial
  | level :: rest, index, s, hts, hlen, hh => by
    have hh0 := hh level rfl
    unfold whirLevels
    simp only [Prog.bind_eq]
    refine QRange.bind_noCQ_allRet (noCQ_foldRounds _ _ _) (allRet_foldRounds _ _ _) ?_
    rintro ⟨s', levelFolds⟩ hs'
    simp only at hs'
    have hdepth : logN - s'.folds.length + level.logInvRate =
        logN - (s.folds.length + level.fold) + level.logInvRate := by rw [hs']
    rcases rest with _ | ⟨next, rest'⟩
    · dsimp only
      refine QRange.bind_noCQ (NoCQ.readN _) fun residual ↦ ?_
      simp only [Prog.pure_eq, Prog.ret_bind]
      refine QRange.bind_noCQ (NoCQ.grindP _) fun _ ↦ ?_
      refine QRange.bind_noCQ_allRet (noCQ_sampleQueriesAux _ _ _)
        (allRet_sampleQueriesAux _ _ _) fun queries hq ↦ ?_
      refine QRange.bind_noCQ NoCQ.sampleE fun lam ↦ ?_
      refine ⟨fun q hq' ht hht ↦ ?_, fun rows ↦ QRange.of_noCQ ?_⟩
      · rw [hh0, Option.some.injEq] at hht
        rw [← hht, ← hdepth]
        exact hq q hq'
      · exact NoCQ.bind trivial fun _ ↦ NoCQ.bind (noCQ_sumcheckRoundPoly _ _ _) fun _ ↦
          NoCQ.bind (noCQ_tailRounds _ _ _) fun _ ↦ NoCQ.require _
    · dsimp only
      show QRange (hts ++ [(levelShape (logN - s'.folds.length) next (3 * 2 ^ next.fold)).1]) _
      have hlen' : (hts ++ [(levelShape (logN - s'.folds.length) next (3 * 2 ^ next.fold)).1]).length
          = index + 1 + 1 := by simp [hlen]
      have hidx : (hts ++ [(levelShape (logN - s'.folds.length) next (3 * 2 ^ next.fold)).1])[index]?
          = hts[index]? := List.getElem?_append_left (by omega)
      refine QRange.bind_noCQ trivial fun _ ↦ ?_
      refine QRange.bind_noCQ (NoCQ.sampleN _) fun _ ↦ ?_
      refine QRange.bind_noCQ NoCQ.readE fun _ ↦ ?_
      refine QRange.bind_noCQ (noCQ_sumcheckRoundPoly _ _ _) fun _ ↦ ?_
      simp only [Prog.pure_eq, Prog.ret_bind]
      refine QRange.bind_noCQ (NoCQ.grindP _) fun _ ↦ ?_
      refine QRange.bind_noCQ_allRet (noCQ_sampleQueriesAux _ _ _)
        (allRet_sampleQueriesAux _ _ _) fun queries hq ↦ ?_
      refine QRange.bind_noCQ NoCQ.sampleE fun lam ↦ ?_
      refine ⟨fun q hq' ht hht ↦ ?_, fun rows ↦ ?_⟩
      · rw [hidx, hh0, Option.some.injEq] at hht
        rw [← hht, ← hdepth]
        exact hq q hq'
      · refine QRange.bind_noCQ trivial fun words ↦ ?_
        refine QRange.bind_noCQ (noCQ_sumcheckRoundPoly _ _ _) fun intro ↦ ?_
        refine qRange_whirLevels logN laneFolds evaluateBasis (next :: rest') (index + 1) _ _
          hlen' fun l hl ↦ ?_
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hl
        subst hl
        rw [List.getElem?_append_right (by omega), glue_folds]
        simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, levelShape, Option.some.injEq]
        omega

/-! ## The deferring verifier -/

/-- **The verifier's queries are in range**, for fixed polynomials' values that neither commit nor
query: the stack is commitment `0`, at the height WHIR's first level samples at. -/
theorem qRange_verifyExecution {ev : Evaluations} (hb : ∀ w p, NoCQ (ev.bytecode w p))
    (hm : ∀ a z r c s, NoCQ (ev.matrices a z r c s)) (bytecode : List K) (publicInput : Digest) :
    QRange [] (verifyExecution ev bytecode publicInput) := by
  unfold verifyExecution
  simp only [Prog.bind_eq]
  refine QRange.bind_noCQ (noCQ_readSizes bytecode) fun r ↦ ?_
  obtain ⟨layout, logInverseRate⟩ := r
  unfold commitStack
  simp only [Prog.bind_eq, Prog.bind_assoc]
  rcases hcfg : deriveConfig layout.stackLog logInverseRate with _ | config
  · trivial
  · rcases config with _ | ⟨level, rest⟩
    · trivial
    · show QRange ([] ++ [(levelShape layout.stackLog level (2 ^ level.fold)).1]) _
      refine QRange.bind_noCQ trivial fun _ ↦ ?_
      refine QRange.bind_noCQ (noCQ_verifyBusBalance hb layout) fun bus ↦ ?_
      refine QRange.bind_noCQ (noCQ_tablePhase layout bus) fun claims ↦ ?_
      refine QRange.bind_noCQ (noCQ_publicInputPhase layout publicInput) fun pc ↦ ?_
      refine QRange.bind_noCQ (noCQ_verifyFlock hm _) fun fr ↦ ?_
      obtain ⟨flockPoint, flockS⟩ := fr
      refine QRange.bind_noCQ (noCQ_ringSwitch flockPoint flockS) fun rr ↦ ?_
      obtain ⟨ringTarget, ringWeight⟩ := rr
      have hlift : Verifier.liftOption (deriveConfig layout.stackLog logInverseRate) =
          Prog.ret (level :: rest) := by rw [hcfg]; rfl
      unfold verifyStackedOpening verifyWhir
      simp only [Prog.bind_eq, hlift, Prog.ret_bind]
      refine QRange.bind_noCQ NoCQ.sampleE fun _ ↦ ?_
      refine QRange.bind_noCQ (noCQ_sumcheckRoundPoly _ _ _) fun _ ↦ ?_
      refine qRange_whirLevels _ _ _ _ 0 _ _ (by simp) fun l hl ↦ ?_
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hl
      subst hl
      simp [levelShape]

/-- The claimed values neither commit nor query. -/
theorem noCQ_claimed_bytecode (c : FixedClaims) (w : List K) (p : List E) :
    NoCQ ((Evaluations.claimed c).bytecode w p) :=
  NoCQ.seq (NoCQ.require _) fun _ ↦ NoCQ.pure _

/-- The claimed values neither commit nor query. -/
theorem noCQ_claimed_matrices (c : FixedClaims) (a z : E) (r c' s : List E) :
    NoCQ ((Evaluations.claimed c).matrices a z r c' s) :=
  NoCQ.seq (NoCQ.require _) fun _ ↦ NoCQ.pure _

/-- **The deferring verifier's queries are in range.** -/
theorem qRange_deferredProgram (c : FixedClaims) (bytecode : List K) (publicInput : Digest) :
    QRange [] (deferredProgram c bytecode publicInput) := by
  unfold deferredProgram
  simp only [Prog.bind_eq]
  exact QRange.bind_any (fun _ _ ↦ trivial)
    (qRange_verifyExecution (noCQ_claimed_bytecode c) (noCQ_claimed_matrices c) _ _)

/-- **The deferring verifier's query steps on an honest proof agree**: when the honest prover of
the deferring verifier's program gives `π` and the strategy's run along the Fiat–Shamir
challenges returns, every query step of the compiled verifier on `π` is one tree's openings. -/
theorem queriesOfWith_deferred_honest (H : Bytes → Digest) (S : Strategy) (fuel : ℕ)
    {c : FixedClaims} {bytecode : List K} {publicInput seed : Digest} {π : Proof}
    (hπ : prove H (deferredProgram c bytecode publicInput) S seed fuel = some π)
    {r : Bool × Digest × List Ev}
    (hfs : fsRun H S fuel (deferredProgram c bytecode publicInput) seed [] = some r) :
    ∀ b ∈ queriesOfWith H (deferredProgram c bytecode publicInput)
      ⟨seed, π.stream, π.openings, []⟩, BatchAgreesWith H b.1 b.2 := by
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hπ
  have h := queriesOfWith_proveFrom H S fuel _ [] seed t.1 t.2 [] [] r hfs (by simp [commits])
    (qRange_deferredProgram c bytecode publicInput) ht
  simpa [commits, rootsOf] using h

end
end LeanVM.E2E.Complete
