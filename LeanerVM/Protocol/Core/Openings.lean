/-
  LeanerVM.Protocol.Core.Openings

  The rows the verifier's replayed openings authenticate are the rows the decoded transcript's
  words have at the positions it reads.
-/

module

public import LeanerVM.Protocol.LeanVmReader
public import LeanerVM.Protocol.Prove.Openings

/-!
# The openings, read off the log

The verifier replayed on a log answers each hash from it, failing where it has no answer. A
replay of the openings that succeeds is their run with every hash answered by the log alone
(`openings_opt_of_replay`), and that run accepts every level's opening against its root
(`OpeningsOk`, `openingsOk_of_run`).

On a consistent log with no collision, every row an opening authenticates against a root is the
row read off the log under that root at its position (`rows_eq_of_merkle`, through Merkle
binding). The level-0 rows read off the log, lanes in reverse, are the rows of the level-0 word
read off the log (`logWord_row_reverse`), and a later level's rows, three limbs a lane, are the
rows of its word (`laterRows_laterWord`). So when the transcript's later words are those read
off the log under the roots the levels carry (`LadderRoots`), and the transcript's positions are
those the walk read, the rows the openings authenticate are the transcript's rows
(`rows_eq_ladderRows`). The algebra the verifier runs counts each level's rows
(`rowCounts_of_algebra`) and reads the walk's wire as the transcript carries it
(`algebra_view`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa ProtocolSpec StepSchedule Verify
open DecodeChain Whir SlotDecoder ChainLog OracleComp OracleSpec

@[expose] public section

namespace Core

/-! ## The openings, answered by the log alone -/

/-- The hash answered by `ans`, failing where it has no answer. -/
private abbrev optImpl
    (ans : List UInt8 → Option Digest) : QueryImpl hashSpec Option := fun t ↦ ans t

/-- A replay that succeeds is the run answered by the log alone, with the same value. -/
private theorem simulateQ_option_of_replay {α : Type} (ans : List UInt8 → Option Digest)
    (oa : OracleComp hashSpec α) {pre : hashSpec.QueryLog} {x : α} {log : hashSpec.QueryLog}
    (h : (simulateQ (QueryLog.replayImpl ans) oa).run pre = some (x, log)) :
    simulateQ (optImpl ans) oa = some x := by
  induction oa using OracleComp.inductionOn generalizing pre x log with
  | pure y =>
    simp only [simulateQ_pure, StateT.run_pure] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    rw [simulateQ_pure]
    rfl
  | query_bind t mx ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at h ⊢
    rcases hu : ans t with _ | u
    · simp [QueryLog.replayImpl, hu] at h
    · have hstep : (QueryLog.replayImpl ans t).run pre = pure (u, pre ++ [⟨t, u⟩]) := by
        simp [QueryLog.replayImpl, hu]
      rw [hstep, pure_bind] at h
      show (ans t).bind _ = _
      rw [hu, Option.bind_some]
      exact ih u h

/-- The reader's morphism answering by `ans` alone. -/
private abbrev optHom (ans : List UInt8 → Option Digest) : Walk
    (OracleComp hashSpec) →ᵐ Walk Option :=
  ReadM.mapHom (simulateQ' (optImpl ans))

private theorem readerOps_opt (ans : List UInt8 → Option Digest) :
    (readerOps hashQuery).map (optHom ans) = readerOps (m := Option) ans := by
  rw [readerOps_hom]
  congr
  funext t
  simp [hashQuery, optImpl]

private theorem walkOpenings_opt (ans : List UInt8 → Option Digest) (nLanes : ℕ) (first : Bool)
    (root : Digest) (shs : List LevelShape) (ls : List WhirLevel) :
    optHom ans (walkOpenings (readerOps hashQuery) nLanes first root shs ls) =
      walkOpenings (readerOps (m := Option) ans) nLanes first root shs ls := by
  rw [← readerOps_opt]
  induction shs generalizing first root ls with
  | nil => simp [walkOpenings]
  | cons sh shs ih =>
    cases ls with
    | nil => simp [walkOpenings]
    | cons l ls => simp [walkOpenings, ih, ChainOps.map]

/-- **The replayed openings, answered by the log alone**: a replay of the openings that succeeds
is their run with every hash answered from the log, failing where it has no answer. -/
theorem openings_opt_of_replay {ans : List UInt8 → Option Digest} {nLanes : ℕ} {first : Bool}
    {root : Digest} {shs : List LevelShape} {ls : List WhirLevel}
    {st : ReaderState PrunedMerklePaths} {log : hashSpec.QueryLog}
    {r : Except ReadError (List (List (List K)) × ReaderState PrunedMerklePaths)}
    {log' : hashSpec.QueryLog}
    (h : runReplay (walkOpenings (readerOps (QueryLog.replayImpl ans)) nLanes first root shs ls)
      st log = some (r, log')) :
    ((walkOpenings (readerOps (m := Option) ans) nLanes first root shs ls).run st).run =
      some r := by
  rw [← walkOpenings_replay] at h
  rw [← walkOpenings_opt]
  exact simulateQ_option_of_replay ans _ h

/-- Every level's opening accepted, answered by `ans`, against its root at its positions, with
its rows. -/
def OpeningsOk (ans : List UInt8 → Option Digest) (nLanes : ℕ) :
    Bool → Digest → List LevelShape → List WhirLevel → List (List (List K)) → Prop
  | first, root, sh :: shs, l :: ls, rows => ∃ r rs, rows = r :: rs ∧
      (∃ paths, merkleVerifyWith (m := Option) ans root (sh.msgLog + sh.rate)
        (rowWordsOf nLanes first sh) (leafWordsOf first sh) l.positions paths = some (some r)) ∧
      OpeningsOk ans nLanes false (l.root.getD root) shs ls rs
  | _, _, _, _, rows => rows = []

/-- A run of the reader answering by `ans` alone. -/
abbrev runOpt {α : Type} (a : Walk Option α) (st : ReaderState PrunedMerklePaths) :
    Option (Except ReadError (α × ReaderState PrunedMerklePaths)) :=
  (a.run st).run

private theorem runOpt_bind {α β : Type} (a : Walk Option α) (f : α → Walk Option β)
    (st : ReaderState PrunedMerklePaths) :
    runOpt (a >>= f) st = match runOpt a st with
      | some (.ok (x, st')) => runOpt (f x) st'
      | some (.error e) => some (.error e)
      | none => none := by
  simp only [runOpt, StateT.run_bind, ExceptT.run_bind]
  rcases ((a.run st).run) with _ | ⟨_ | ⟨x, st'⟩⟩ <;> rfl

private theorem runOpt_nextOpening (ans : List UInt8 → Option Digest) (root : Digest)
    (depth rowWords leafWords : ℕ) (ps : List ℕ) (fs : FsState) (stream : List E)
    (o : PrunedMerklePaths) (ms : List PrunedMerklePaths) :
    runOpt ((readerOps (m := Option) ans).nextOpening root depth rowWords leafWords ps)
        ⟨fs, stream, o :: ms⟩ =
      (merkleVerifyWith ans root depth rowWords leafWords ps o).map fun r ↦ match r with
        | some a => .ok (a, ⟨fs, stream, ms⟩)
        | none => .error .invalidMerkleOpening := by
  rw [show (readerOps (m := Option) ans).nextOpening root depth rowWords leafWords ps =
    Reader.nextOpening (merkleVerifyWith ans root depth rowWords leafWords ps) from rfl]
  rcases h : merkleVerifyWith ans root depth rowWords leafWords ps o with _ | _ | a <;>
    simp [Reader.nextOpening, runOpt, h]

private theorem runOpt_nextOpening_nil (ans : List UInt8 → Option Digest) (root : Digest)
    (depth rowWords leafWords : ℕ) (ps : List ℕ) (fs : FsState) (stream : List E) :
    runOpt ((readerOps (m := Option) ans).nextOpening root depth rowWords leafWords ps)
        ⟨fs, stream, []⟩ = some (.error .missingHint) := rfl

/-- A run of the openings in `Option` that succeeds accepts every level's opening. -/
theorem openingsOk_of_run (ans : List UInt8 → Option Digest) (nLanes : ℕ) :
    ∀ (shs : List LevelShape) (ls : List WhirLevel) (first : Bool) (root : Digest)
      (st : ReaderState PrunedMerklePaths) (rows : List (List (List K)))
      (st' : ReaderState PrunedMerklePaths),
      runOpt (walkOpenings (readerOps (m := Option) ans) nLanes first root shs ls) st =
        some (.ok (rows, st')) → OpeningsOk ans nLanes first root shs ls rows
  | [], _, _, _, _, _, _, h => by
    simp only [walkOpenings] at h
    cases h
    rfl
  | _ :: _, [], _, _, _, _, _, h => by
    simp only [walkOpenings] at h
    cases h
    rfl
  | sh :: shs, l :: ls, first, root, st, rows, st', h => by
    simp only [walkOpenings] at h
    rw [runOpt_bind] at h
    rcases st with ⟨fs, stream, _ | ⟨o, ms⟩⟩
    · rw [runOpt_nextOpening_nil] at h
      cases h
    rw [runOpt_nextOpening] at h
    rcases hm : merkleVerifyWith ans root (sh.msgLog + sh.rate) (rowWordsOf nLanes first sh)
        (leafWordsOf first sh) l.positions o with _ | _ | r <;> rw [hm] at h
    · cases h
    · cases h
    simp only [Option.map_some] at h
    rw [runOpt_bind] at h
    rcases hr : runOpt (walkOpenings (readerOps (m := Option) ans) nLanes false (l.root.getD root)
        shs ls) ⟨fs, stream, ms⟩ with _ | ⟨_ | ⟨rs, st₂⟩⟩ <;> rw [hr] at h
    · cases h
    · cases h
    simp only [runOpt, StateT.run_pure, ExceptT.run_pure, Option.pure_def, Option.some.injEq,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨r, rs, rfl, ⟨o, hm⟩, openingsOk_of_run ans nLanes shs ls false _ _ rs st₂ hr⟩



/-! ## The rows an opening authenticates are the log's -/

/-- Every row the opening of a level authenticates against `root`, answered from a log with no
collision, is the leaf image of the row read off the log at its position; so the rows, in query
order, are the leaves at the positions, given the leaves are those images. -/
private theorem rows_eq_of_merkle {l : hashSpec.QueryLog} (hc : QueryLog.Consistent l)
    (hcoll : ¬ QueryLog.HasCollision l) {root : Digest} {depth rowWords leafWords : ℕ}
    {ps : List ℕ} {paths : PrunedMerklePaths} {r : List (List K)}
    (hv : merkleVerifyWith (m := Option) (MerkleTree.logAnswer l) root depth rowWords leafWords
      ps paths = some (some r))
    {t : ℕ} (hlen : r.length = t) (leaf : Fin (2 ^ depth) → List K)
    (hleaf : rowWords ≤ leafWords → ∀ (p : Fin (2 ^ depth)) row,
      extractRows l root depth rowWords leafWords p = some row → leaf p = leafImage leafWords row) :
    r = List.ofFn fun q : Fin t ↦ leaf (positionsOf t depth ps q) := by
  have hbind := binding_of_log l [] (MerkleTree.logAnswer l)
    (fun q d h ↦ by simpa using MerkleTree.mem_of_logAnswer_eq_some h) [root] root
    (List.mem_singleton_self _) depth rowWords leafWords ps paths r hv
    (fun e₁ h₁ e₂ h₂ h ↦ hc e₁ (by simpa using h₁) e₂ (by simpa using h₂) h)
    (fun ⟨e₁, h₁, e₂, h₂, hne, heq⟩ ↦ hcoll
      ⟨e₁, by simpa using h₁, e₂, by simpa using h₂, hne, heq⟩)
    (fun ⟨e, he, _⟩ ↦ by simp at he)
  obtain ⟨-, -, hrw, -, hlt, -, -⟩ := merkleVerifyWith_option_eq_some hv
  have hps : ps.length = r.length := by simpa using congrArg List.length hbind
  apply List.ext_getElem (by simp [hlen])
  intro i h₁ h₂
  have hi : i < ps.length := by omega
  have hp : ps[i] < 2 ^ depth := hlt _ (mem_sortedUnique.mpr (List.getElem_mem hi))
  have hb := congrArg (·[i]?) hbind
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem h₁,
    Option.map_some] at hb
  obtain ⟨row, hrow, hrow'⟩ := Option.map_eq_some_iff.mp (Option.some.inj hb)
  simp only [List.getElem_ofFn, positionsOf, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]
  rw [hleaf hrw ⟨ps[i] % 2 ^ depth, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ row (by
    simpa [Nat.mod_eq_of_lt hp] using hrow), hrow']

/-! ## Rows read off a log -/

private theorem length_wordsOfBytes : ∀ q : List UInt8,
    (LeanerVM.Protocol.wordsOfBytes q).length = q.length / 8
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest => by
    simp only [LeanerVM.Protocol.wordsOfBytes, List.length_cons, length_wordsOfBytes rest]
    omega
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] => by simp [LeanerVM.Protocol.wordsOfBytes]

/-- A row read off a log has the row's width. -/
private theorem length_of_extractRows {l : hashSpec.QueryLog} {root : Digest}
    {depth rowWords leafWords p : ℕ} {row : List K}
    (h : extractRows l root depth rowWords leafWords p = some row) : row.length = rowWords := by
  unfold extractRows MerkleTree.extractLeaf at h
  obtain ⟨d, -, hd⟩ := Option.bind_eq_some_iff.mp h
  unfold MerkleTree.leafPreimage at hd
  obtain ⟨e, -, he⟩ := List.exists_of_findSome?_eq_some hd
  split at he
  · unfold leafRow? at he
    dsimp only at he
    split at he
    · rename_i hq
      cases he
      rw [length_wordsOfBytes, List.length_drop, hq.1]
      omega
    · cases he
  · cases he

/-- Level 0's row read off a log, lanes in reverse, is the stored row's leaf image. -/
theorem logWord_row_reverse {l : hashSpec.QueryLog} {root : Digest} {depth n ℓ t : ℕ}
    (hn : n ≤ 2 ^ ℓ) (p : Fin (2 ^ depth)) {row : List K}
    (hrow : extractRows l root depth n (2 ^ ℓ) p = some row) :
    ((logWord l root depth n ℓ t).row p).toList.reverse = leafImage (2 ^ ℓ) row := by
  have hlen := length_of_extractRows hrow
  have hw : (wordRows l root depth n ℓ)[p] = LeanerVM.Protocol.laneRow ℓ row := by
    simp [wordRows, extractAllRows_eq, hrow]
  show ((wordRows l root depth n ℓ)[p]).toList.reverse = _
  rw [hw, LeanerVM.Protocol.laneRow, leafImage]
  have : (Vector.ofFn fun u : Fin (2 ^ ℓ) ↦ row.reverse.getD u 0).toList =
      row.reverse ++ List.replicate (2 ^ ℓ - row.length) 0 := by
    apply List.ext_getElem (by simp; omega)
    intro i h₁ h₂
    simp only [Vector.toList_ofFn, List.getElem_ofFn]
    by_cases hi : i < row.length
    · rw [List.getElem_append_left (by simpa using hi)]
      simp [List.getD_eq_getElem?_getD, hi]
    · rw [List.getElem_append_right (by simpa using hi)]
      simp [List.getD_eq_getElem?_getD, hi]
  rw [this, List.reverse_append, List.reverse_replicate, List.reverse_reverse]

private theorem flatMap_limbs : ∀ (m : ℕ) (xs : List K), xs.length = 3 * m →
    ((List.range m).map fun i ↦ E.ofLimbs (xs.getD (3 * i) 0) (xs.getD (3 * i + 1) 0)
      (xs.getD (3 * i + 2) 0)).flatMap (fun e ↦ [e.limb 0, e.limb 1, e.limb 2]) = xs
  | 0, xs, h => by simp_all
  | m + 1, xs, h => by
    have ht : (xs.take (3 * m)).length = 3 * m := by rw [List.length_take, h]; omega
    have hm := flatMap_limbs m (xs.take (3 * m)) ht
    have hcongr : ((List.range m).map fun i ↦ E.ofLimbs (xs.getD (3 * i) 0)
        (xs.getD (3 * i + 1) 0) (xs.getD (3 * i + 2) 0)) =
        ((List.range m).map fun i ↦ E.ofLimbs ((xs.take (3 * m)).getD (3 * i) 0)
          ((xs.take (3 * m)).getD (3 * i + 1) 0) ((xs.take (3 * m)).getD (3 * i + 2) 0)) := by
      refine List.map_congr_left fun i hi ↦ ?_
      rw [List.mem_range] at hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
      simp [show 3 * i < 3 * m by omega, show 3 * i + 1 < 3 * m by omega,
        show 3 * i + 2 < 3 * m by omega]
    rw [List.range_succ, List.map_append, List.flatMap_append, hcongr, hm]
    conv_rhs => rw [← List.take_append_drop (3 * m) xs]
    congr 1
    have hd : (xs.drop (3 * m)).length = 3 := by simp [h]; omega
    refine List.ext_getElem (by simp [hd]) fun i h₁ h₂ ↦ ?_
    have hi : i < 3 := by simpa using h₁
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      limb_ofLimbs, List.getElem_drop]
    interval_cases i
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 3 * m < xs.length by omega)]
    · simp [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show 3 * m + 1 < xs.length by omega)]
    · simp [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show 3 * m + 2 < xs.length by omega)]

/-- A later level's row read off a log, stored three limbs a lane, is the stored row. -/
private theorem laterRows_laterWord {l : hashSpec.QueryLog} {sh : Whir.Shape} {κ : ℕ}
    {root : Digest}
    (p : Fin (2 ^ (κ + sh.R))) {row : List K}
    (hrow : extractRows l root (κ + sh.R) (3 * 2 ^ sh.ℓ) (3 * 2 ^ sh.ℓ) p = some row) :
    (Prove.laterRows (LeanVmReader.laterWord l sh κ (some root)))[p] = row := by
  have hlen := length_of_extractRows hrow
  have hw : (LeanVmReader.laterWord l sh κ (some root)).row p =
      (Verify.laneRow false sh.ℓ row).getD (Vector.replicate _ 0) := by
    simp [LeanVmReader.laterWord, extractAllRows_eq, hrow]
  rw [Prove.laterRows, Fin.getElem_fin, Vector.getElem_ofFn, hw]
  simp only [Verify.laneRow, Bool.false_eq_true, ↓reduceIte, RoundPoly.ofList?, List.length_map,
    List.length_range, ↓reduceDIte, Option.getD_some]
  exact flatMap_limbs (2 ^ sh.ℓ) row hlen

/-! ## The algebra reads the walk's wire viewed -/

private theorem whirLevels_view : ∀ (shs : List LevelShape) (first : Bool) (n : ℕ) (W : Weight E n)
    (claim : E) (quad : Vector E 3) (ls : List WhirLevel) (rows : List (List (List K))),
    whirLevels first n W claim quad shs (List.zipWith DecodeChain.WhirLevel.view shs ls) rows =
      whirLevels first n W claim quad shs ls rows
  | [], _, _, _, _, _, ls, _ => by cases ls <;> simp [whirLevels]
  | _ :: _, _, _, _, _, _, [], _ => by simp [whirLevels]
  | _ :: _, _, _, _, _, _, _ :: _, [] => by simp [whirLevels]
  | sh :: shs, first, n, W, claim, quad, l :: ls, r :: rs => by
    simp only [List.zipWith_cons_cons, whirLevels, DecodeChain.WhirLevel.view,
      Prove.positionsOf_positionsList, whirLevels_view shs]

/-- **The algebra reads the walk's wire as a transcript carries it**: the roots erased and the
positions reduced change nothing. -/
theorem algebra_view (prog : Program) (s : Sizes) (input : PublicInput) (shs : List LevelShape)
    (w : Wire) (rows : List (List (List K))) :
    algebra prog s input shs
      (DecodeChain.Wire.view shs w) rows = algebra prog s input shs w rows := by
  simp only [algebra, DecodeChain.Wire.view, whirCheck, whirLevels_view]

/-! ## The levels' row counts -/

/-- Each level's rows are as many as its queries, up to the last level. -/
def RowCounts : List LevelShape → List (List (List K)) → Prop
  | sh :: shs, r :: rs => r.length = sh.queries ∧ (sh.final = false → RowCounts shs rs)
  | _, _ => True

private theorem rowCounts_of_whirLevels : ∀ (shs : List LevelShape) (first : Bool) (n : ℕ)
    (W : Weight E n) (claim : E) (quad : Vector E 3) (ls : List WhirLevel)
    (rows : List (List (List K))),
    whirLevels first n W claim quad shs ls rows = true → RowCounts shs rows
  | [], _, _, _, _, _, _, _, _ => trivial
  | _ :: _, _, _, _, _, _, [], _, h => by simp [whirLevels] at h
  | _ :: _, _, _, _, _, _, _ :: _, [], h => by simp [whirLevels] at h
  | sh :: shs, first, n, W, claim, quad, l :: ls, r :: rs, h => by
    unfold whirLevels at h
    rcases hf₀ : replayFolds claim quad l.folds with _ | ⟨claim', quad', cs⟩ <;>
      simp only [hf₀] at h
    · cases h
    by_cases hh : sh.fold + sh.msgLog = n ∧ cs.length = sh.fold ∧ r.length = sh.queries
    · refine ⟨hh.2.2, fun hf ↦ ?_⟩
      rw [dite_eq_left hh] at h
      rcases hm : r.mapM (Verify.laneRow first sh.fold) with _ | lanes <;> simp only [hm] at h
      · cases h
      split at h
      · cases h
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · exact rowCounts_of_whirLevels shs false _ _ _ _ ls rs h
      · cases h
    · rw [dite_eq_right hh] at h
      cases h

private theorem rowCounts_of_whirCheck {μ : ℕ} {shs : List LevelShape} {W : Weight E μ} {target : E}
    {first : List E} {ls : List WhirLevel} {rows : List (List (List K))}
    (h : whirCheck μ shs W target first ls rows = true) : RowCounts shs rows := by
  unfold whirCheck at h
  split at h
  · split at h
    · exact rowCounts_of_whirLevels _ true _ _ _ _ _ _ h
    · cases h
  · cases h

/-- The rows the algebra accepts are as many as each level's queries. -/
theorem rowCounts_of_algebra {prog : Program} {s : Sizes} {input : PublicInput}
    {shs : List LevelShape} {w : Wire} {rows : List (List (List K))}
    (h : algebra prog s input shs w rows = true) : RowCounts shs rows := by
  unfold algebra at h
  rcases hb : leanVmBus prog s input w.bus with _ | b
  · simp [hb] at h
  rcases ht : tableStep (leanVm prog s) b w.table with _ | t
  · simp [hb, ht] at h
  rcases hp : pubStep (leanVm prog s) t w.pub with _ | p
  · simp [hb, ht, hp] at h
  rcases hf : flockStep (leanVm prog s) (flockRegion prog s Blake2sFlock.blake2sFlockSpec) rfl
      blake2sRows p w.flock with _ | f
  · simp [hb, ht, hp, hf] at h
  simp only [hb, ht, hp, hf] at h
  exact rowCounts_of_whirCheck h

/-! ## The rows of the ladder -/

/-- The roots the walk's levels carry, each later word of the transcript read off the log under
the root before it. -/
def LadderRoots (l : hashSpec.QueryLog) : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) →
    (seqSpec L.steps).FullTranscript → List WhirLevel → Prop
  | _, _, .last _ _, _, _ => True
  | _, _, @Ladder.cons _ sh' κ' L, t, lv :: ls =>
    (∃ root, lv.root = some root ∧ Prove.levelWord t = LeanVmReader.laterWord l sh' κ'
      (some root)) ∧
      LadderRoots l L (levelWire t).2 ls
  | _, _, .cons _ _, _, [] => False

private theorem positionsList_injective {t b : ℕ} {f g : Fin t → Fin (2 ^ b)}
    (h : positionsList f = positionsList g) : f = g := by
  funext q
  have := congrArg (·[q.val]?) h
  simp only [positionsList, List.getElem?_ofFn, Fin.eta] at this
  exact Fin.ext (by simpa using this)

/-- **The rows the openings authenticate are the transcript's rows**, level by level: each
level's rows, read off the log at the positions the walk read, are the rows of the transcript's
word there. -/
theorem rows_eq_ladderRows {l : hashSpec.QueryLog} (hc : QueryLog.Consistent l)
    (hcoll : ¬ QueryLog.HasCollision l) (nLanes : ℕ) :
    ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (first : Bool) (root : Digest)
      (leaf : Fin (2 ^ (κ + sh.R)) → List K) (t : (seqSpec L.steps).FullTranscript)
      (ls : List WhirLevel) (rows : List (List (List K))),
      (rowWordsOf nLanes first ⟨sh.ℓ, κ, sh.R, sh.t, false⟩ ≤
          leafWordsOf first ⟨sh.ℓ, κ, sh.R, sh.t, false⟩ →
        ∀ (p : Fin (2 ^ (κ + sh.R))) row, extractRows l root (κ + sh.R)
          (rowWordsOf nLanes first ⟨sh.ℓ, κ, sh.R, sh.t, false⟩)
          (leafWordsOf first ⟨sh.ℓ, κ, sh.R, sh.t, false⟩) p = some row →
        leaf p = leafImage (leafWordsOf first ⟨sh.ℓ, κ, sh.R, sh.t, false⟩) row) →
      LadderRoots l L t ls →
      OpeningsOk (MerkleTree.logAnswer l) nLanes first root L.shapes ls rows →
      ladderWire L t = List.zipWith DecodeChain.WhirLevel.view L.shapes ls →
      RowCounts L.shapes rows →
      rows = Prove.ladderRows L leaf t
  | _, _, .last sh nf, first, root, leaf, t, ls, rows, hleaf, _, hop, hw, hcnt => by
    rcases ls with _ | ⟨lv, ls⟩
    · simp [Whir.Ladder.shapes, ladderWire] at hw
    obtain ⟨r, rs, rfl, ⟨paths, hv⟩, hrest⟩ := hop
    have hrs : rs = [] := hrest
    subst hrs
    simp only [Whir.Ladder.shapes, ladderWire, List.zipWith_cons_cons, List.cons.injEq] at hw
    have hpos : Prove.finalPositions t = positionsOf sh.t (nf + 1 + sh.R) lv.positions :=
      positionsList_injective (congrArg WhirLevel.positions hw.1)
    simp only [Prove.ladderRows, hpos, List.cons.injEq, and_true]
    exact rows_eq_of_merkle hc hcoll hv hcnt.1 leaf hleaf
  | _, _, @Ladder.cons sh sh' κ' L, first, root, leaf, t, ls, rows, hleaf, hroots, hop, hw,
      hcnt => by
    rcases ls with _ | ⟨lv, ls⟩
    · exact hroots.elim
    obtain ⟨⟨root', hroot', hword⟩, hroots'⟩ := hroots
    obtain ⟨r, rs, rfl, ⟨paths, hv⟩, hrest⟩ := hop
    simp only [Whir.Ladder.shapes, ladderWire, List.zipWith_cons_cons, List.cons.injEq] at hw
    have hpos : Prove.levelPositions t = positionsOf sh.t (Kap sh' κ' + sh.R) lv.positions :=
      positionsList_injective (congrArg WhirLevel.positions hw.1)
    simp only [Prove.ladderRows, hpos, List.cons.injEq]
    refine ⟨rows_eq_of_merkle hc hcoll hv hcnt.1 leaf hleaf, ?_⟩
    rw [hroot', Option.getD_some] at hrest
    refine rows_eq_ladderRows hc hcoll nLanes L false root' _ _ ls rs (fun _ p row hrow ↦ ?_)
      hroots' hrest hw.2 (hcnt.2 rfl)
    rw [hword, laterRows_laterWord p hrow]
    simp [leafWordsOf]

end Core

end

end LeanerVM.Protocol
