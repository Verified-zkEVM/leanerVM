/-
  LeanVM.E2E.Complete.Count.Whir

  The deferring verifier opens at most 368 leaves, each of at most 192 words (L17, package A):
  before WHIR it commits only the stack (`2^6` words a leaf) and queries nothing, and WHIR's
  levels commit leaves of `3·2^fold ≤ 192` words and open at most their tabulated query counts,
  which sum to at most 368 over a ladder.
-/

module

public import LeanVM.E2E.Complete.Count.Prog

/-!
# The deferring verifier's leaves

`LeafBound W p n` (`Count/Prog.lean`): every commitment of `p` has width at most `W`, and `p`
opens at most `n` leaves. Here `leafBound_deferredProgram`: the deferring verifier, for every
claims `c`, at `whirLeafWidth = 192` and `whirLeaves = 368`.

* the ladder (`Whir.ladder`): every level folds at most `initialFold = 6` variables
  (`ladder_fold_le`: `shape`'s first fold is `initialFold`, `levelsFrom`'s are
  `min subsequentFold _`), and its query counts sum to at most 368 (`ladder_queries_sum_le`: they
  are a `queryTable` entry, every entry's sum checked by `decide`);
* a level samples at most its count of positions (`allRet_sampleQueriesAux_length`);
* WHIR's levels (`leafBound_whirLevels`, by induction on the levels as `qRange_whirLevels`): a
  level opens its sampled positions and commits the next level's leaves of `3·2^fold` words;
* the phases before WHIR neither commit nor query (`NoCQ`, `CapsRange.lean`), and the stack's
  leaves have `2^fold ≤ 64` words (`leafBound_verifyExecution`, as `qRange_verifyExecution`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The ladder -/

/-- The levels after the first fold at most `subsequentFold` variables. -/
theorem levelsFrom_fold_le : ∀ (fuel remaining prevFold prevRate reduction : ℕ),
    ∀ g ∈ Whir.levelsFrom fuel remaining prevFold prevRate reduction, g.1 ≤ Whir.subsequentFold
  | 0, _, _, _, _ => by simp [Whir.levelsFrom]
  | fuel + 1, remaining, prevFold, prevRate, reduction => by
    intro g hg
    simp only [Whir.levelsFrom] at hg
    split at hg
    · simp at hg
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact Nat.min_le_left _ _
      · exact levelsFrom_fold_le fuel _ _ _ _ g hg

/-- Every level of the geometry folds at most `initialFold` variables. -/
theorem shape_fold_le (μ logInvRate : ℕ) :
    ∀ g ∈ Whir.shape μ logInvRate, g.1 ≤ Whir.initialFold := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact Nat.le_refl _
  · exact (levelsFrom_fold_le _ _ _ _ _ g hg).trans (by decide)

/-- Pairing the geometry with the counts keeps the folds' bound and drops counts. -/
theorem zipWith_level_bounds (k : ℕ) : ∀ (gs : List (ℕ × ℕ)) (qs : List ℕ),
    (∀ g ∈ gs, g.1 ≤ k) →
      (∀ l ∈ List.zipWith (fun (g : ℕ × ℕ) q ↦ (⟨g.1, g.2, q⟩ : Whir.Level)) gs qs, l.fold ≤ k) ∧
      ((List.zipWith (fun (g : ℕ × ℕ) q ↦ (⟨g.1, g.2, q⟩ : Whir.Level)) gs qs).map
        (·.queries)).sum ≤ qs.sum
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | g :: gs, q :: qs, hg => by
    have ih := zipWith_level_bounds k gs qs fun g' hg' ↦ hg g' (List.mem_cons_of_mem _ hg')
    refine ⟨fun l hl ↦ ?_, ?_⟩
    · rcases List.mem_cons.mp hl with rfl | hl
      · exact hg g List.mem_cons_self
      · exact ih.1 l hl
    · simp only [List.zipWith_cons_cons, List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left ih.2 q

/-- Every entry of the query table sums to at most `368`. -/
theorem queryTable_sum_le : ∀ row ∈ Whir.queryTable, ∀ e ∈ row, e.sum ≤ 368 := by
  decide

/-- What every element of a list and the default satisfy, `getD` does. -/
theorem getD_of_forall_mem {γ : Type} {P : γ → Prop} {d : γ} (hd : P d) :
    ∀ (l : List γ) (i : ℕ), (∀ x ∈ l, P x) → P (l.getD i d) := by
  intro l i hl
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact hd
  | some x => exact hl x (List.mem_of_getElem? h)

/-- **Every level of a ladder folds at most `6` variables.** -/
theorem ladder_fold_le {μ logInvRate : ℕ} {ls : List Whir.Level}
    (h : Whir.ladder μ logInvRate = some ls) : ∀ l ∈ ls, l.fold ≤ 6 := by
  unfold Whir.ladder at h
  split at h
  · dsimp only at h
    split at h
    · cases h
      exact (zipWith_level_bounds 6 _ _ (shape_fold_le μ logInvRate)).1
    · cases h
  · cases h

/-- **A ladder's query counts sum to at most `368`**: they are a `queryTable` entry. -/
theorem ladder_queries_sum_le {μ logInvRate : ℕ} {ls : List Whir.Level}
    (h : Whir.ladder μ logInvRate = some ls) : (ls.map (·.queries)).sum ≤ 368 := by
  unfold Whir.ladder at h
  split at h
  · dsimp only at h
    split at h
    · cases h
      refine (zipWith_level_bounds 6 _ _ (shape_fold_le μ logInvRate)).2.trans ?_
      refine getD_of_forall_mem (P := fun e : List ℕ ↦ e.sum ≤ 368) (by decide) _ _ ?_
      exact getD_of_forall_mem (P := fun row : List (List ℕ) ↦ ∀ e ∈ row, e.sum ≤ 368)
        (by simp) _ _ queryTable_sum_le
    · cases h
  · cases h

/-! ## The query sampling -/

/-- **A level samples at most its count of positions.** -/
theorem allRet_sampleQueriesAux_length (depth : ℕ) : ∀ (fuel remaining : ℕ),
    AllRet (fun qs : List ℕ ↦ qs.length ≤ remaining) (sampleQueriesAux depth fuel remaining)
  | 0, _ => Nat.zero_le _
  | fuel + 1, remaining => by
    simp only [sampleQueriesAux]
    split
    · exact Nat.zero_le _
    · simp only [Prog.bind_eq]
      refine AllRet.bind (fun e _ ↦ ?_) _ (allRet_true _)
      refine AllRet.bind (fun rest hrest ↦ ?_) _ (allRet_sampleQueriesAux_length depth fuel _)
      show (_ ++ rest).length ≤ remaining
      simp only [List.length_append, List.length_map, List.length_range]
      have h1 := Nat.min_le_right (192 / depth) remaining
      have h2 : rest.length ≤ remaining - min (192 / depth) remaining := hrest
      omega

/-! ## WHIR's levels -/

/-- A deeper level's leaves have at most `whirLeafWidth` words. -/
theorem three_mul_two_pow_le_whirLeafWidth {fold : ℕ} (h : fold ≤ 6) :
    3 * 2 ^ fold ≤ whirLeafWidth :=
  (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by decide) h)).trans (by decide)

/-- **WHIR's levels open at most their query counts' sum of leaves**, every committed leaf of at
most `whirLeafWidth` words, when every level folds at most `6` variables. -/
theorem leafBound_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (n : ℕ),
      (∀ l ∈ levels, l.fold ≤ 6) → (levels.map (·.queries)).sum ≤ n →
      LeafBound whirLeafWidth (whirLevels logN laneFolds evaluateBasis index levels s) n
  | [], _, _, _, _, _ => trivial
  | level :: rest, index, s, n, hf, hn => by
    simp only [List.map_cons, List.sum_cons] at hn
    unfold whirLevels
    simp only [Prog.bind_eq]
    refine LeafBound.bind_noCQ (noCQ_foldRounds _ _ _) fun r ↦ ?_
    obtain ⟨s', levelFolds⟩ := r
    rcases rest with _ | ⟨next, rest'⟩
    · dsimp only
      refine LeafBound.bind_noCQ (NoCQ.readN _) fun residual ↦ ?_
      simp only [Prog.pure_eq, Prog.ret_bind]
      refine LeafBound.bind_noCQ (NoCQ.grindP _) fun _ ↦ ?_
      refine LeafBound.bind_noCQ_allRet (noCQ_sampleQueriesAux _ _ _)
        (allRet_sampleQueriesAux_length _ _ _) fun queries hq ↦ ?_
      refine LeafBound.bind_noCQ NoCQ.sampleE fun lam ↦ ?_
      refine ⟨by simp at hn; omega, fun rows ↦ LeafBound.of_noCQ ?_⟩
      exact NoCQ.bind trivial fun _ ↦ NoCQ.bind (noCQ_sumcheckRoundPoly _ _ _) fun _ ↦
        NoCQ.bind (noCQ_tailRounds _ _ _) fun _ ↦ NoCQ.require _
    · dsimp only
      refine ⟨three_mul_two_pow_le_whirLeafWidth (hf next (by simp)), ?_⟩
      refine LeafBound.bind_noCQ trivial fun _ ↦ ?_
      refine LeafBound.bind_noCQ (NoCQ.sampleN _) fun _ ↦ ?_
      refine LeafBound.bind_noCQ NoCQ.readE fun _ ↦ ?_
      refine LeafBound.bind_noCQ (noCQ_sumcheckRoundPoly _ _ _) fun _ ↦ ?_
      simp only [Prog.pure_eq, Prog.ret_bind]
      refine LeafBound.bind_noCQ (NoCQ.grindP _) fun _ ↦ ?_
      refine LeafBound.bind_noCQ_allRet (noCQ_sampleQueriesAux _ _ _)
        (allRet_sampleQueriesAux_length _ _ _) fun queries hq ↦ ?_
      refine LeafBound.bind_noCQ NoCQ.sampleE fun lam ↦ ?_
      refine ⟨by omega, fun rows ↦ ?_⟩
      refine LeafBound.bind_noCQ trivial fun words ↦ ?_
      refine LeafBound.bind_noCQ (noCQ_sumcheckRoundPoly _ _ _) fun intro ↦ ?_
      exact leafBound_whirLevels logN laneFolds evaluateBasis (next :: rest') (index + 1) _ _
        (fun l hl ↦ hf l (List.mem_cons_of_mem _ hl)) (by omega)

/-! ## The deferring verifier -/

/-- **The verifier opens at most `whirLeaves` leaves of at most `whirLeafWidth` words**, for
fixed polynomials' values that neither commit nor query. -/
theorem leafBound_verifyExecution {ev : Evaluations} (hb : ∀ w p, NoCQ (ev.bytecode w p))
    (hm : ∀ a z r c s, NoCQ (ev.matrices a z r c s)) (bytecode : List K) (publicInput : Digest) :
    LeafBound whirLeafWidth (verifyExecution ev bytecode publicInput) whirLeaves := by
  unfold verifyExecution
  simp only [Prog.bind_eq]
  refine LeafBound.bind_noCQ (noCQ_readSizes bytecode) fun r ↦ ?_
  obtain ⟨layout, logInverseRate⟩ := r
  unfold commitStack
  simp only [Prog.bind_eq, Prog.bind_assoc]
  rcases hcfg : deriveConfig layout.stackLog logInverseRate with _ | config
  · trivial
  · rcases config with _ | ⟨level, rest⟩
    · trivial
    · have hf := ladder_fold_le hcfg
      refine ⟨(Nat.pow_le_pow_right (by decide) (hf level (by simp))).trans (by decide), ?_⟩
      refine LeafBound.bind_noCQ trivial fun _ ↦ ?_
      refine LeafBound.bind_noCQ (noCQ_verifyBusBalance hb layout) fun bus ↦ ?_
      refine LeafBound.bind_noCQ (noCQ_tablePhase layout bus) fun claims ↦ ?_
      refine LeafBound.bind_noCQ (noCQ_publicInputPhase layout publicInput) fun pc ↦ ?_
      refine LeafBound.bind_noCQ (noCQ_verifyFlock hm _) fun fr ↦ ?_
      obtain ⟨flockPoint, flockS⟩ := fr
      refine LeafBound.bind_noCQ (noCQ_ringSwitch flockPoint flockS) fun rr ↦ ?_
      obtain ⟨ringTarget, ringWeight⟩ := rr
      have hlift : Verifier.liftOption (deriveConfig layout.stackLog logInverseRate) =
          Prog.ret (level :: rest) := by rw [hcfg]; rfl
      unfold verifyStackedOpening verifyWhir
      simp only [Prog.bind_eq, hlift, Prog.ret_bind]
      refine LeafBound.bind_noCQ NoCQ.sampleE fun _ ↦ ?_
      refine LeafBound.bind_noCQ (noCQ_sumcheckRoundPoly _ _ _) fun _ ↦ ?_
      exact leafBound_whirLevels _ _ _ _ 0 _ _ hf (ladder_queries_sum_le hcfg)

/-- **The deferring verifier opens at most `whirLeaves` leaves of at most `whirLeafWidth`
words**, for every claims `c`. -/
theorem leafBound_deferredProgram (c : FixedClaims) (bytecode : List K) (pi : Digest) :
    LeafBound whirLeafWidth (deferredProgram c bytecode pi) whirLeaves := by
  unfold deferredProgram
  simp only [Prog.bind_eq]
  have := LeafBound.bind (f := fun _ ↦ (pure true : Prog Bool)) (n₂ := 0)
    (leafBound_verifyExecution (noCQ_claimed_bytecode c) (noCQ_claimed_matrices c) bytecode pi)
    fun _ ↦ trivial
  exact this

end
end LeanVM.E2E.Complete
