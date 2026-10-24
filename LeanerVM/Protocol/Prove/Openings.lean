/-
  LeanerVM.Protocol.Prove.Openings

  The honest prover's proof passes the verifier's setup, its openings have the shapes the ladder
  fixes, and the verifier's openings read the prover's back: every committed word opened at its
  level's positions authenticates against the root the walk read, with the rows of the
  transcript's words at the transcript's positions.
-/

module

public import LeanerVM.Protocol.Prove.ReadBack

/-!
# The openings and the setup

The honest prover (`LeanerVM.Protocol.Prove`) keeps every commitment and every level's positions
in its book, and opens each committed word at its level's positions after the stream
(`hintOpenings`). The verifier reads the announcement off the head of the stream (`setup?`),
derives the WHIR ladder (`ladderOf`), checks the openings' number and shapes before any hash
(`openingsOk`), and after the chain walk authenticates each opening against the root the walk read
(`walkOpenings`, by `merkleVerifyWith`).

* `ladderRows`, `rowsOf`: the rows the openings carry, on a transcript of the compiled protocol:
  each level's word's rows' leaf images at the level's positions, the level-0 rows lanes in reverse
  and the later ones three limbs a lane, as the prover stores them (`level0Rows`, `laterRows`);
* `runs_hintOpenings`: what the prover's openings write;
* `reads_openings`: the walk's openings read them back as `ladderRows` of the transcript, every
  opening authenticated (`merkleVerifyWith_merkleOpen`);
* `openingsOk_openings`: they have the shapes the levels fix;
* `setup?_of_announce`, `ladderOf_leanIsaChain`, `leanIsaChain_walk`: an admissible announcement
  passes the setup, and the verifier's levels are the deployed chain's.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa Whir CompPoly
open OracleComp OracleSpec ProtocolSpec StepSchedule DecodeChain

@[expose] public section

namespace Prove

/-! ## The rows of a transcript -/

/-- The rows the openings of a chain of levels carry on its transcript: each level's word, given
as its rows' leaf images, at the level's positions, in query order; a level with a successor
hands on its word, stored as three limbs a lane. -/
def ladderRows : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) →
    (Fin (2 ^ (κ + sh.R)) → List K) → (seqSpec L.steps).FullTranscript → List (List (List K))
  | _, _, .last _ _, leaf, t => [List.ofFn fun q ↦ leaf (finalPositions t q)]
  | _, _, @Ladder.cons _ sh' κ' L, leaf, t =>
    (List.ofFn fun q ↦ leaf (levelPositions t q)) ::
      ladderRows L (fun p ↦ leafImage (3 * 2 ^ sh'.ℓ) (laterRows (levelWord t))[p])
        (levelWire t).2

/-- **The rows the openings carry, on a transcript of the compiled protocol**: the level-0
word's rows, lanes in reverse, then each later level's word's rows, three limbs a lane, every row's
leaf image at its level's positions, level by level. -/
def rowsOf (I : M3Instance) {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (t : (listBindingSpec I sh κ L).FullTranscript) : List (List (List K)) :=
  ladderRows L (fun p ↦ ((level0Word t).row p).toList.reverse) (ladderPart t)

/-! ## The prover's openings -/

/-- The openings of the commitments at the positions, in order. -/
def openingsOf (cs : List (Σ k, MerkleCommitment k)) (pss : List (List ℕ)) :
    List PrunedMerklePaths :=
  (cs.zip pss).map fun p ↦ merkleOpen p.1.2 p.2

variable (H : List UInt8 → Id Digest)

/-- Openings appended in a loop are appended in order. -/
private theorem runs_forIn_openings : ∀ (l : List ((Σ k, MerkleCommitment k) × List ℕ))
    {s s' : PState} {u : PUnit},
    proveSem.Runs (forIn l PUnit.unit fun x _ ↦ match x with
        | (c, ps) => do
          StateT.lift (Writer.hintOpening (m := Id) (merkleOpen c.2 ps))
          return ForInStep.yield PUnit.unit) s u s' →
      s'.1 = s.1 ∧ s'.2.fs = s.2.fs ∧ s'.2.stream = s.2.stream ∧
        s'.2.merkle.toList = s.2.merkle.toList ++ l.map fun p ↦ merkleOpen p.1.2 p.2
  | [], s, s', u, h => by
    obtain ⟨-, rfl⟩ := proveSem.pure_inv h
    simp
  | p :: l, s, s', u, h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, sm, h₁, h₂⟩ := proveSem.bind_inv h
    obtain ⟨v, sm', h₃, h₄⟩ := proveSem.bind_inv h₁
    obtain ⟨rfl, rfl⟩ := proveSem.pure_inv h₄
    obtain ⟨hb, hw⟩ := runs_lift.mp h₃
    rcases sm with ⟨bkm, wsm⟩
    simp only [Writer.hintOpening, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      StateT.run, OptionT.run, pure, OptionT.pure, OptionT.mk] at hw
    cases hw
    obtain ⟨h₅, h₆, h₇, h₈⟩ := runs_forIn_openings l h₂
    refine ⟨h₅.trans hb, h₆, h₇, ?_⟩
    rw [h₈]
    simp

/-- A failing computation does not run. -/
private theorem not_runs_failure {α : Type} {s s' : PState} {a : α} :
    ¬ proveSem.Runs (failure : ProveM Id α) s a s' := by
  intro h
  change (((failure : ProveM Id α).run s.1).run s.2).run = _ at h
  simp at h

/-- **What the prover's openings write**: every commitment kept opened at its level's
positions, in order, after the openings so far; nothing else changes. -/
theorem runs_hintOpenings {s s' : PState} {u : Unit}
    (h : proveSem.Runs (hintOpenings (m := Id)) s u s') :
    s'.1 = s.1 ∧ s'.2.fs = s.2.fs ∧ s'.2.stream = s.2.stream ∧
      s'.2.merkle.toList =
        s.2.merkle.toList ++ openingsOf s.1.commits.toList s.1.positions.toList := by
  unfold hintOpenings at h
  obtain ⟨b, sm, h₁, h₂⟩ := proveSem.bind_inv h
  obtain ⟨rfl, rfl⟩ : b = s.1 ∧ sm = s := by
    rcases sm with ⟨bk, ws⟩
    change (((get : ProveM Id Book).run s.1).run s.2).run = some ((b, bk), ws) at h₁
    simp only [StateT.run_get, StateT.run_pure, OptionT.run_pure] at h₁
    cases h₁
    exact ⟨rfl, rfl⟩
  split at h₂
  · obtain ⟨_, _, h₃, -⟩ := proveSem.bind_inv h₂
    exact absurd h₃ not_runs_failure
  · obtain ⟨_, sm, h₃, h₄⟩ := proveSem.bind_inv h₂
    obtain ⟨-, rfl⟩ := proveSem.pure_inv h₄
    exact runs_forIn_openings _ h₃

/-! ## The walk reads the openings back -/

/-- The rows at raw positions standing for a transcript's are the rows at the transcript's, in
query order. -/
private theorem map_eq_ofFn_of_posRead {t b : ℕ} {ps : List ℕ} {pos : Fin t → Fin (2 ^ b)}
    (h : PosRead ps pos) (rowsV : Vector (List K) (2 ^ b)) (f : List K → List K) :
    ps.map (fun q ↦ f (rowsV[q]?.getD [])) = List.ofFn fun q ↦ f rowsV[pos q] := by
  obtain ⟨hlt, hlen, rfl⟩ := h
  apply List.ext_getElem (by simp [hlen])
  intro i h₁ h₂
  have hi' : i < ps.length := by simpa using h₁
  have hi : ps[i] < 2 ^ b := hlt _ (List.getElem_mem _)
  simp [Verify.positionsOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
    Nat.mod_eq_of_lt hi, Vector.getElem?_eq_getElem hi]

/-- An opening of a commitment is read back as the leaf images of the rows at the positions,
authenticated against the commitment's root. -/
private theorem reads_nextOpening {k rowWords leafWords : ℕ} (rows : Vector (List K) (2 ^ k))
    (ps : List ℕ) (hrw : rowWords ≤ leafWords) (hw : ∀ row ∈ rows.toList, row.length = rowWords)
    (hne : ps ≠ []) (hlt : ∀ q ∈ ps, q < 2 ^ k) {w w' : WriterState PrunedMerklePaths}
    (hfs : w'.fs = w.fs) (hst : w'.stream = w.stream)
    (hm : w'.merkle.toList =
      w.merkle.toList ++ [merkleOpen (merkleCommitWith H leafWords rows) ps]) :
    Reads ((Verify.readerOps H).nextOpening (merkleCommitWith H leafWords rows).root k rowWords
      leafWords ps) w w' (ps.map fun q ↦ leafImage leafWords (rows[q]?.getD [])) := by
  have ha : merkleVerifyWith (m := Id) H (merkleCommitWith H leafWords rows).root k rowWords
      leafWords ps (merkleOpen (merkleCommitWith H leafWords rows) ps) =
      pure (some (ps.map fun q ↦ leafImage leafWords (rows[q]?.getD []))) :=
    merkleVerifyWith_merkleOpen H rows ps hrw hw hne hlt
  refine ⟨[], [merkleOpen (merkleCommitWith H leafWords rows) ps], by simp [hst], hm,
    fun _ _ ↦ ?_⟩
  rw [hfs]
  simp [Verify.readerOps, Reader.nextOpening, ha]
  rfl

/-- Rows stored three limbs a lane are three words a lane wide. -/
private theorem length_laterRows {ℓ b t : ℕ} (x : Word ℓ b t) :
    ∀ row ∈ (laterRows x).toList, row.length = 3 * 2 ^ ℓ := by
  intro row hrow
  obtain ⟨y, rfl⟩ : ∃ y : Fin (2 ^ b), row = (laterRows x)[y] := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
    exact ⟨⟨i, by simpa using hi⟩, by simp⟩
  simp [laterRows, List.length_flatMap, mul_comm]

variable (nLanes : ℕ)

/-- **The walk's openings read the prover's back**, on a chain of levels from a level whose word,
stored as `rowsV`, the walk holds the root of: every level's opening, authenticated against the
root the walk holds for it, read as the rows of the transcript's words at the transcript's
positions (`ladderRows`). -/
theorem reads_openings : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (first : Bool)
    (rowsV : Vector (List K) (2 ^ (κ + sh.R))),
    Verify.rowWordsOf nLanes first ⟨sh.ℓ, κ, sh.R, sh.t, false⟩ ≤
      Verify.leafWordsOf first ⟨sh.ℓ, κ, sh.R, sh.t, false⟩ →
    (∀ row ∈ rowsV.toList,
      row.length = Verify.rowWordsOf nLanes first ⟨sh.ℓ, κ, sh.R, sh.t, false⟩) →
    (∀ x ∈ L.shapes, 0 < x.queries) →
    ∀ {t : (seqSpec L.steps).FullTranscript} {ls cs pss}, LadderRead H L t ls cs pss →
    ∀ {w w' : WriterState PrunedMerklePaths}, w'.fs = w.fs → w'.stream = w.stream →
    w'.merkle.toList = w.merkle.toList ++ openingsOf
      (⟨κ + sh.R, merkleCommitWith H (Verify.leafWordsOf first ⟨sh.ℓ, κ, sh.R, sh.t, false⟩)
        rowsV⟩ :: cs) pss →
    Reads (Verify.walkOpenings (Verify.readerOps H) nLanes first
        (merkleCommitWith H (Verify.leafWordsOf first ⟨sh.ℓ, κ, sh.R, sh.t, false⟩) rowsV).root
        L.shapes ls) w w'
      (ladderRows L (fun p ↦
        leafImage (Verify.leafWordsOf first ⟨sh.ℓ, κ, sh.R, sh.t, false⟩) rowsV[p]) t)
  | _, _, .last sh nf, first, rowsV, hrw, hw, hq, t, ls, cs, pss, h, w, w', hfs, hst, hm => by
    obtain ⟨l, rfl, rfl, rfl, hp⟩ := h
    have hne : l.positions ≠ [] := fun he ↦ by
      have h₀ := hq _ (List.mem_singleton_self _)
      have h₁ := hp.2.1
      rw [he] at h₁
      simp only [List.length_nil] at h₁
      exact absurd h₀ (by rw [← h₁]; exact Nat.lt_irrefl 0)
    have h₁ := reads_nextOpening H rowsV l.positions hrw hw hne hp.1 hfs hst (by rw [hm]; rfl)
    refine h₁.bind ((Reads.pure _ _).bind_ret ?_)
    rw [map_eq_ofFn_of_posRead hp]
    rfl
  | _, _, @Ladder.cons sh sh' κ' L, first, rowsV, hrw, hw, hq, t, ls, cs, pss, h, w, w', hfs, hst,
      hm => by
    obtain ⟨l, ls', cs', pss', rfl, rfl, rfl, hp, ho, hl⟩ := h
    have hne : l.positions ≠ [] := fun he ↦ by
      have h₀ := hq _ (List.mem_cons_self ..)
      have h₁ := hp.2.1
      rw [he] at h₁
      simp only [List.length_nil] at h₁
      exact absurd h₀ (by rw [← h₁]; exact Nat.lt_irrefl 0)
    let o := merkleOpen (merkleCommitWith H (Verify.leafWordsOf first
      ⟨sh.ℓ, Kap sh' κ', sh.R, sh.t, false⟩) rowsV) l.positions
    let w₁ : WriterState PrunedMerklePaths := { w with merkle := w.merkle.push o }
    have h₁ := reads_nextOpening H rowsV l.positions hrw hw hne hp.1 (w := w) (w' := w₁) rfl rfl
      (by simp [w₁, o])
    have h₂ := reads_openings L false (laterRows (levelWord t)) le_rfl (length_laterRows _)
      (fun x hx ↦ hq x (List.mem_cons_of_mem _ hx)) hl (w := w₁) (w' := w') hfs hst
      (by rw [hm]; simp [w₁, o, openingsOf, Verify.leafWordsOf])
    simp only [Whir.Ladder.shapes, Verify.walkOpenings, ho, Option.getD_some]
    refine h₁.bind (h₂.bind_ret ?_)
    rw [map_eq_ofFn_of_posRead hp]
    rfl

/-! ## The openings' shapes -/

/-- A level of a pruned opening supplies at most one sibling per opened node. -/
private theorem length_levelSiblings_le {D : Type} {n : ℕ} (level : Vector D n) :
    ∀ ps : List ℕ, (MerkleTree.levelSiblings level ps).length ≤ ps.length
  | [] => by simp [MerkleTree.levelSiblings]
  | [i] => by
    simp only [MerkleTree.levelSiblings]
    cases level[MerkleTree.sibling i]? <;> simp
  | i :: j :: rest => by
    simp only [MerkleTree.levelSiblings]
    split_ifs
    · have := length_levelSiblings_le level rest
      simp only [List.length_cons]
      omega
    · have := length_levelSiblings_le level (j :: rest)
      cases level[MerkleTree.sibling i]? <;> simp only [Option.toList_none, Option.toList_some,
        List.nil_append, List.singleton_append, List.length_cons] at this ⊢ <;> omega

/-- The opened nodes' parents are at most as many as the nodes. -/
private theorem length_parentPositions_le :
    ∀ ps : List ℕ, (MerkleTree.parentPositions ps).length ≤ ps.length
  | [] => by simp [MerkleTree.parentPositions]
  | [i] => by simp [MerkleTree.parentPositions]
  | i :: j :: rest => by
    simp only [MerkleTree.parentPositions]
    split_ifs
    · have := length_parentPositions_le rest
      simp only [List.length_cons]
      omega
    · have := length_parentPositions_le (j :: rest)
      simp only [List.length_cons] at this ⊢
      omega

/-- A pruned opening of a tree of depth `k` has at most `k` siblings per opened leaf. -/
private theorem length_siblings_le {D : Type} :
    ∀ {k : ℕ} (lv : MerkleTree.Levels D k) (ps : List ℕ), (lv.siblings ps).length ≤ k * ps.length
  | _, .top _, _ => by simp [MerkleTree.Levels.siblings]
  | k + 1, .cons level above, ps => by
    simp only [MerkleTree.Levels.siblings, List.length_append]
    calc _ ≤ ps.length + k * ps.length := Nat.add_le_add (length_levelSiblings_le level ps)
          ((length_siblings_le above _).trans
            (Nat.mul_le_mul_left k (length_parentPositions_le ps)))
      _ = (k + 1) * ps.length := by ring

/-- The sorted distinct positions are at most as many as the positions. -/
private theorem length_sortedUnique_le (ps : List ℕ) : (sortedUnique ps).length ≤ ps.length := by
  unfold sortedUnique
  exact (List.destutter_sublist _ _).length_le.trans (List.length_mergeSort ps).le

/-- An honest opening of a level has the shape the level fixes. -/
private theorem openingOk_level {k rowWords leafWords t : ℕ} (rows : Vector (List K) (2 ^ k))
    (hw : ∀ row ∈ rows.toList, row.length = rowWords) {ps : List ℕ} (hlen : ps.length = t)
    (hlt : ∀ q ∈ ps, q < 2 ^ k) :
    (decide ((merkleOpen (merkleCommitWith H leafWords rows) ps).leafData.length ≤ t) &&
      (merkleOpen (merkleCommitWith H leafWords rows) ps).leafData.all (·.length = rowWords) &&
      decide ((merkleOpen (merkleCommitWith H leafWords rows) ps).siblingHashes.length ≤
        t * k)) = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨?_, fun row hrow ↦ ?_⟩, ?_⟩
  · simp only [merkleOpen, List.length_map]
    exact hlen ▸ length_sortedUnique_le ps
  · simp only [merkleOpen, List.mem_map] at hrow
    obtain ⟨q, hq, rfl⟩ := hrow
    have hq' : q < 2 ^ k := hlt q (mem_sortedUnique.mp hq)
    simp only [merkleCommitWith, Vector.getElem?_eq_getElem hq', Option.getD_some]
    exact hw _ (by simp)
  · simp only [merkleOpen]
    refine (length_siblings_le _ _).trans ?_
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right k (hlen ▸ length_sortedUnique_le ps)

/-- **The prover's openings have the shapes the levels fix**: one per level, at most one row per
query, every row of the level's width, at most as many siblings as the queries' paths have
nodes. -/
theorem openingsOk_openings : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (first : Bool)
    (rowsV : Vector (List K) (2 ^ (κ + sh.R))),
    (∀ row ∈ rowsV.toList,
      row.length = Verify.rowWordsOf nLanes first ⟨sh.ℓ, κ, sh.R, sh.t, false⟩) →
    ∀ {t : (seqSpec L.steps).FullTranscript} {ls cs pss}, LadderRead H L t ls cs pss →
    Verify.openingsOk nLanes first L.shapes (openingsOf
      (⟨κ + sh.R, merkleCommitWith H (Verify.leafWordsOf first ⟨sh.ℓ, κ, sh.R, sh.t, false⟩)
        rowsV⟩ :: cs) pss) = true
  | _, _, .last sh nf, first, rowsV, hw, t, ls, cs, pss, h => by
    obtain ⟨l, rfl, rfl, rfl, hp⟩ := h
    have := openingOk_level H rowsV hw hp.2.1 hp.1 (leafWords :=
      Verify.leafWordsOf first ⟨sh.ℓ, nf + 1, sh.R, sh.t, false⟩)
    simp only [Whir.Ladder.shapes, openingsOf, List.zip_cons_cons, List.zip_nil_right,
      List.map_cons, List.map_nil, Verify.openingsOk, Bool.and_true] at this ⊢
    exact this
  | _, _, @Ladder.cons sh sh' κ' L, first, rowsV, hw, t, ls, cs, pss, h => by
    obtain ⟨l, ls', cs', pss', rfl, rfl, rfl, hp, -, hl⟩ := h
    have h₁ := openingOk_level H rowsV hw hp.2.1 hp.1 (leafWords :=
      Verify.leafWordsOf first ⟨sh.ℓ, Kap sh' κ', sh.R, sh.t, false⟩)
    have h₂ := openingsOk_openings L false (laterRows (levelWord t)) (length_laterRows _) hl
    simp only [Whir.Ladder.shapes, openingsOf, List.zip_cons_cons, List.map_cons,
      Verify.openingsOk] at h₁ h₂ ⊢
    rw [h₁, Bool.true_and]
    exact h₂

/-! ## The setup -/

/-- Scalars sent are appended to the stream; the openings are left. -/
theorem stream_addScalars : ∀ (xs : List E) {w w' : WriterState PrunedMerklePaths},
    ((Writer.addScalars H xs).run w).run = some ((), w') →
      w'.stream.toList = w.stream.toList ++ xs ∧ w'.merkle = w.merkle
  | [], w, w', h => by
    cases h
    simp
  | x :: xs, w, w', h => by
    have h₁ : ((Writer.addScalar H x).run w).run = some ((), { w with
        fs := Id.run (w.fs.observe H x), stream := w.stream.push x }) := rfl
    change ((Writer.addScalar H x >>= fun _ ↦ Writer.addScalars H xs).run w).run = _ at h
    rw [StateT.run_bind, OptionT.run_bind, h₁] at h
    obtain ⟨h₂, h₃⟩ := stream_addScalars xs h
    exact ⟨by rw [h₂]; simp, h₃⟩

/-- A proof whose stream opens with the announcement of sizes and a rate passing the setup checks
passes the setup with them. -/
theorem setup?_of_announce {prog : Program} {s : Sizes} {ρ : ℕ} {p : Proof PrunedMerklePaths}
    (hok : setupOk prog s ρ = true) (h : p.stream.take 8 = announcement s ρ) :
    Verify.setup? prog p = some (s, ρ) := by
  simp [Verify.setup?, Proof.announced?, h, decodeAnnouncement_announcement hok, hok]

/-- A fact about the window of WHIR's parameters, decided on it. -/
private theorem window {P : ℕ → ℕ → Prop}
    (key : ∀ μ < Whir.maxLogStack + 1, ∀ r < Whir.maxLogInvRate + 1, Whir.Admissible μ r → P μ r)
    {μ r : ℕ} (h : Whir.Admissible μ r) : P μ r :=
  key μ (Nat.lt_succ_of_le h.2.1) r (Nat.lt_succ_of_le h.2.2.2) h

/-- Every level of an admissible ladder folds at least one variable; the first folds six. -/
private theorem ladder_folds {μ r : ℕ} (h : Whir.Admissible μ r) :
    (Whir.ladder μ r).all fun ls ↦ ls.all (0 < ·.fold) && ls.head?.all (·.fold == 6) :=
  window (P := fun μ r ↦
    (Whir.ladder μ r).all fun ls ↦ ls.all (0 < ·.fold) && ls.head?.all (·.fold == 6))
    (by decide +kernel) h

/-- Every level of an admissible ladder queries a position, and a squeeze gives one. -/
private theorem ladder_shapes_ok {μ r : ℕ} (h : Whir.Admissible μ r) :
    (Whir.ladder μ r).all fun ls ↦ (Verify.levelShapes μ ls).all
      fun x ↦ decide (0 < x.queries) && decide (0 < 192 / (x.msgLog + x.rate)) :=
  window (P := fun μ r ↦ (Whir.ladder μ r).all fun ls ↦ (Verify.levelShapes μ ls).all
      fun x ↦ decide (0 < x.queries) && decide (0 < 192 / (x.msgLog + x.rate)))
    (by decide +kernel) h

/-- The chain of levels the deployed parameters build walks the levels' shapes. -/
private theorem chainOf_shapes : ∀ (rem : ℕ) (ps : List (Whir.Level × ℚ)) (c : Chain),
    chainOf rem ps = some c → (∀ p ∈ ps, 0 < p.1.fold) →
      c.ladder.shapes = Verify.levelShapes rem (ps.map Prod.fst) ∧ c.κ + c.sh.ℓ = rem
  | _, [], c, h, _ => by simp [chainOf] at h
  | rem, [(l, η)], c, h, hf => by
    have hl := Shape.ofFold_ℓ (fold := l.fold) (hf _ (List.mem_singleton_self _)) l.logInvRate
      l.queries
    simp only [chainOf] at h
    split at h
    · cases h
    · rename_i nf hnf
      split_ifs at h
      cases h
      refine ⟨?_, ?_⟩
      · simp only [Whir.Ladder.shapes, List.map_cons, List.map_nil, Verify.levelShapes, hl, hnf]
        rfl
      · show nf + 1 + (Shape.ofFold l.fold l.logInvRate l.queries).ℓ = rem
        rw [hl]
        change rem - l.fold = nf + 1 at hnf
        omega
  | rem, (l, η) :: p :: rest, c, h, hf => by
    have hl := Shape.ofFold_ℓ (fold := l.fold) (hf _ (List.mem_cons_self ..)) l.logInvRate
      l.queries
    simp only [chainOf] at h
    obtain ⟨c', hc', h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h
    cases h
    obtain ⟨ih₁, ih₂⟩ := chainOf_shapes _ _ c' hc' (fun q hq ↦ hf q (List.mem_cons_of_mem _ hq))
    have hpos : 0 < rem - l.fold := by
      have : 0 < c'.sh.ℓ := Nat.succ_pos _
      omega
    refine ⟨?_, ?_⟩
    · simp only [Whir.Ladder.shapes, List.map_cons, Verify.levelShapes, hl, ih₁]
      congr 2
      simp only [Kap]
      omega
    · simp only [Kap, hl]
      omega

/-- **The verifier's levels are the deployed chain's**: at an admissible announcement and rate,
the verifier's ladder exists and its levels' shapes are the shapes the deployed chain of the
compiled protocol walks. -/
private theorem ladderOf_leanIsaChain {prog : Program} {s : Sizes} (hs : s.Admissible prog) {ρ : ℕ}
    (hρ : validRate ρ) : ∃ levels, Verify.ladderOf prog s ρ = some levels ∧
      Verify.levelShapes (Verify.stackMu prog s) levels =
        (leanIsaChain prog s hs ρ hρ).ladder.shapes ∧
      levels.all (0 < ·.fold) ∧ levels.head?.all (·.fold == 6) := by
  have ha := admissible_of_sizes hs hρ
  obtain ⟨ls, hls⟩ := Option.isSome_iff_exists.mp (Whir.ladder_isSome ha)
  have hsl := Whir.slacks_length ha
  rw [hls] at hsl
  obtain ⟨es, hes, hlen⟩ : ∃ es, Whir.slacks (leanIsaμ prog s) ρ = some es ∧
      es.length = ls.length := by
    rcases h : Whir.slacks (leanIsaμ prog s) ρ with _ | es
    · rw [h] at hsl
      cases hsl
    · rw [h] at hsl
      exact ⟨es, rfl, Option.some.inj hsl⟩
  have hc : chainOf (leanIsaμ prog s) (ls.zip es) = some (leanIsaChain prog s hs ρ hρ) := by
    have h₁ : Whir.deployed (leanIsaμ prog s) ρ = chainOf (leanIsaμ prog s) (ls.zip es) := by
      simp only [Whir.deployed, hls, hes, Option.bind_some]
    rw [← h₁]
    exact (Option.some_get (deployed_isSome ha)).symm
  have hf := ladder_folds ha
  rw [hls] at hf
  simp only [Option.all_some, Bool.and_eq_true] at hf
  obtain ⟨hf₁, hf₂⟩ := hf
  refine ⟨ls, hls, ?_, hf₁, hf₂⟩
  obtain ⟨h₁, -⟩ := chainOf_shapes _ _ _ hc (fun p hp ↦ by
    have := List.all_eq_true.mp hf₁ p.1 (List.of_mem_zip hp).1
    simpa using this)
  rw [h₁, List.map_fst_zip (by omega)]

/-- A chain of levels walks at least one level; the first is the chain's first shape. -/
private theorem Ladder.shapes_cons : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ),
    ∃ x xs, L.shapes = x :: xs ∧ x.fold = sh.ℓ
  | _, _, .last _ _ => ⟨_, _, rfl, rfl⟩
  | _, _, .cons _ _ => ⟨_, _, rfl, rfl⟩

/-- **The deployed chain at leanVM, as the verifier walks it**: at an admissible announcement and
rate, the verifier's ladder exists and walks the deployed chain's shapes; every level queries a
position, a squeeze gives one, and level 0 folds six variables. -/
theorem leanIsaChain_walk {prog : Program} {s : Sizes} (hs : s.Admissible prog) {ρ : ℕ}
    (hρ : validRate ρ) : ∃ levels, Verify.ladderOf prog s ρ = some levels ∧
      Verify.levelShapes (Verify.stackMu prog s) levels =
        (leanIsaChain prog s hs ρ hρ).ladder.shapes ∧
      (∀ x ∈ (leanIsaChain prog s hs ρ hρ).ladder.shapes,
        0 < x.queries ∧ 0 < 192 / (x.msgLog + x.rate)) ∧
      (leanIsaChain prog s hs ρ hρ).sh.ℓ = 6 := by
  obtain ⟨levels, hl, hsh, -, hf₂⟩ := ladderOf_leanIsaChain hs hρ
  refine ⟨levels, hl, hsh, fun x hx ↦ ?_, ?_⟩
  · have hok := ladder_shapes_ok (admissible_of_sizes hs hρ)
    change Verify.ladderOf prog s ρ = _ at hl
    rw [show Whir.ladder (leanIsaμ prog s) ρ = some levels from hl] at hok
    simp only [Option.all_some, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok x (hsh ▸ hx)
  · obtain ⟨x, xs, hx, hfold⟩ := Ladder.shapes_cons (leanIsaChain prog s hs ρ hρ).ladder
    rcases levels with _ | ⟨l, ls⟩
    · rw [hx] at hsh
      simp [Verify.levelShapes] at hsh
    · have hl6 : l.fold = 6 := by simpa using hf₂
      have hhead : x.fold = l.fold := by
        rcases ls with _ | ⟨l', ls'⟩ <;> simp only [Verify.levelShapes, hx,
          List.cons.injEq] at hsh <;> rw [← hsh.1]
      rw [← hfold, hhead, hl6]

/-- The committed lanes are at most `2 ^ 6`: level 0's leaf holds them. -/
theorem nLanes_le (prog : Program) (s : Sizes) : Verify.nLanes prog s ≤ 2 ^ 6 := by
  have hb := blocks_fits prog s
  have hμ : 15 ≤ leanIsaμ prog s := le_max_right _ _
  have hd : 2 ^ leanIsaμ prog s = 2 ^ 6 * 2 ^ (Verify.stackMu prog s - Whir.initialFold) := by
    rw [← pow_add]
    congr 1
    simp only [Verify.stackMu, Whir.initialFold]
    omega
  have hpos := Nat.two_pow_pos (Verify.stackMu prog s - Whir.initialFold)
  rw [hd] at hb
  unfold Verify.nLanes
  refine max_le Nat.one_le_two_pow (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpos).mpr ?_))
  have : (2 : ℕ) ^ 6 = 64 := by norm_num
  rw [this] at hb ⊢
  omega

/-- A reader that reads back a whole proof from the empty proof, then the end of the stream and
the openings: its value. -/
theorem run_of_reads {β : Type} {rd : Verify.Walk Id β} {fs : FsState}
    {w' : WriterState PrunedMerklePaths} {b : β} (h : Reads rd ⟨fs, #[], #[]⟩ w' b) :
    ((do let x ← rd; Reader.finish; return x : Verify.Walk Id β).run'
      ⟨fs, w'.stream.toList, w'.merkle.toList⟩).run = Except.ok b := by
  obtain ⟨xs, ms, h₁, h₂, h₃⟩ := h
  simp only [List.nil_append] at h₁ h₂
  have h₄ := h₃ [] []
  simp only [List.append_nil] at h₄
  rw [h₁, h₂]
  simp only [StateT.run'_eq, StateT.run_bind, ExceptT.run_map, ExceptT.run_bind]
  rw [show (StateT.run rd ⟨fs, xs, ms⟩).run = _ from h₄]
  rfl

end Prove

end
end LeanerVM.Protocol
