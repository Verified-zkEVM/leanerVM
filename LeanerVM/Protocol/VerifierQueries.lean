/-
  LeanerVM.Protocol.VerifierQueries

  The hash queries of the executable verifier at the random oracle, bounded for every proof: the
  chain walk's in closed form in the sizes, the openings' by the shapes the setup checks before
  any hash, maximised over the admissible sizes.
-/

module

public import LeanerVM.Protocol.Verify.Count
public import LeanerVM.Protocol.RandomOracle
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import LeanerVM.Protocol.ToVCVio.MerkleQueries

/-!
# The verifier's queries

`queryGrade` is the property of a walk on the proof reader at the random oracle that every run of
it asks at most `n` queries (`IsTotalQueryBound`) and leaves the openings unread. The proof
reader's primitives have their counts under it (`readerOps_graded`: a scalar one query, a challenge
one, a root two, a nonce three), so the chain walk asks at most `queryCounts.chain` queries
(`walkChain_grade`). An opening asks at most a query per stored row and per row and level of the
tree (`isTotalQueryBound_merkleVerifyWith`), and the setup checks the openings' shapes before any
hash (`openingsOk`).

`queryCount prog input s shs` is the bound at the sizes `s` and the levels `shs`;
`verifierQueries prog input` its maximum over the admissible sizes and rates, and
`verifierQueries_bound`: for every proof, the verifier at the random oracle asks at most
`verifierQueries prog input` queries.

Classification: T4 in the random-oracle model, the budget: the verifier's query bound that the
random-oracle bound's error is charged at (`misbehaves_rom`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa OracleComp OracleSpec Verify

@[expose] public section

namespace VerifierQueries

/-- The verifier's walks at the random oracle. -/
abbrev W : Type → Type := Walk (OracleComp hashSpec)

/-- A walk's run from a state, as an oracle computation. -/
abbrev runAt {α : Type} (a : W α) (st : ReaderState PrunedMerklePaths) :
    OracleComp hashSpec (Except ReadError (α × ReaderState PrunedMerklePaths)) :=
  (a.run st).run

private theorem runAt_pure {α : Type} (x : α) (st : ReaderState PrunedMerklePaths) :
    runAt (pure x : W α) st = pure (.ok (x, st)) := rfl

private theorem runAt_bind {α β : Type} (a : W α) (f : α → W β)
    (st : ReaderState PrunedMerklePaths) :
    runAt (a >>= f) st = runAt a st >>= fun r ↦ match r with
      | .ok p => runAt (f p.1) p.2
      | .error e => pure (.error e) := by
  simp only [runAt, StateT.run_bind, ExceptT.run_bind]
  congr 1
  funext r
  cases r <;> rfl

/-- `pure` asks no query. -/
private theorem isTotalQueryBound_pure {α : Type} (x : α) (n : ℕ) :
    IsTotalQueryBound (pure x : OracleComp hashSpec α) n :=
  isQueryBound_pure x n _ _

/-- **The walks that ask at most `n` queries** on every run, from any state, and leave the
openings unread. -/
def queryGrade : MonadGrade W where
  P a n := ∀ st, IsTotalQueryBound (runAt a st) n ∧
    ∀ r ∈ support (runAt a st), ∀ p, r = .ok p → p.2.merkle = st.merkle
  pure x st := by
    refine ⟨isTotalQueryBound_pure _ _, fun r hr p hp ↦ ?_⟩
    rw [runAt_pure, mem_support_pure_iff] at hr
    subst hr
    cases hp
    rfl
  bind {α β a f n k} ha hf st := by
    rw [runAt_bind]
    refine ⟨isTotalQueryBound_bind (ha st).1 fun r ↦ ?_, fun r hr p hp ↦ ?_⟩
    · cases r with
      | ok p => exact (hf p.1 p.2).1
      | error e => exact isTotalQueryBound_pure _ _
    · rw [mem_support_bind_iff] at hr
      obtain ⟨r₁, hr₁, hr⟩ := hr
      cases r₁ with
      | ok p₁ => exact ((hf p₁.1 p₁.2).2 r hr p hp).trans ((ha st).2 _ hr₁ p₁ rfl)
      | error e =>
        rw [mem_support_pure_iff] at hr
        subst hr
        cases hp

/-- A walk that asks no query and keeps the openings. -/
private theorem pure_grade {α : Type} {a : W α}
    (f : ReaderState PrunedMerklePaths → Except ReadError (α × ReaderState PrunedMerklePaths))
    (ha : ∀ st, runAt a st = pure (f st)) (hf : ∀ st p, f st = .ok p → p.2.merkle = st.merkle) :
    queryGrade.P a 0 := fun st ↦
  ⟨by rw [ha]; exact isTotalQueryBound_pure _ _, fun r hr p hp ↦ by
    rw [ha, mem_support_pure_iff] at hr
    subst hr
    exact hf st p hp⟩

private theorem get_grade : queryGrade.P (get : W (ReaderState PrunedMerklePaths)) 0 :=
  pure_grade (fun st ↦ .ok (st, st)) (fun _ ↦ rfl) fun _ _ h ↦ by cases h; rfl

private theorem modify_grade (f : ReaderState PrunedMerklePaths → ReaderState PrunedMerklePaths)
    (hf : ∀ st, (f st).merkle = st.merkle) : queryGrade.P (modify f : W Unit) 0 :=
  pure_grade (fun st ↦ .ok ((), f st)) (fun _ ↦ rfl) fun st _ h ↦ by cases h; exact hf st

private theorem throw_grade {α : Type} (e : ReadError) : queryGrade.P (throw e : W α) 0 :=
  pure_grade (fun _ ↦ .error e) (fun _ ↦ rfl) fun _ _ h ↦ nomatch h

/-- Oracle computations that ask at most `n` queries. -/
private def ocGrade : MonadGrade (OracleComp hashSpec) where
  P c n := IsTotalQueryBound c n
  pure x := isTotalQueryBound_pure x 0
  bind ha hf := isTotalQueryBound_bind ha hf

private theorem runAt_monadLift {α : Type} (c : OracleComp hashSpec α)
    (st : ReaderState PrunedMerklePaths) :
    runAt (liftM c : W α) st = (fun x ↦ .ok (x, st)) <$> c := by
  simp only [runAt, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk,
    StateT.run_lift]
  rw [ExceptT.run_bind]
  show (Except.ok <$> c) >>= _ = _
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp, pure_bind]
  rfl

private theorem lift_grade {α : Type} {c : OracleComp hashSpec α} {n : ℕ} (hc : ocGrade.P c n) :
    queryGrade.P (liftM c : W α) n := fun st ↦
  ⟨by rw [runAt_monadLift]; exact (isQueryBound_map_iff _ _ _ _ _).mpr hc, fun r hr p hp ↦ by
    rw [runAt_monadLift, support_map, Set.mem_image] at hr
    obtain ⟨x, -, rfl⟩ := hr
    cases hp
    rfl⟩

/-- A hash is one query. -/
private theorem isTotalQueryBound_hashQuery (t : List UInt8) :
    IsTotalQueryBound (hashQuery t) 1 := by
  have h := (isTotalQueryBound_query_bind_iff (spec := hashSpec) (t := t)
    (mx := (pure : Digest → OracleComp hashSpec Digest)) (n := 1)).mpr
    ⟨Nat.one_pos, fun u ↦ isTotalQueryBound_pure u 0⟩
  rwa [bind_pure] at h

private theorem hashQuery_grade (t : List UInt8) : ocGrade.P (hashQuery t) 1 :=
  isTotalQueryBound_hashQuery t

private theorem takeRaw_grade : queryGrade.P (Reader.takeRaw (m := OracleComp hashSpec)
    (M := PrunedMerklePaths)) 0 := by
  unfold Reader.takeRaw
  refine queryGrade.of_eq (queryGrade.bind (k := 0) get_grade fun st ↦ ?_) rfl
  split
  · exact throw_grade _
  · exact queryGrade.of_eq (queryGrade.bind (modify_grade _ fun _ ↦ rfl) fun _ ↦
      queryGrade.pure _) rfl

private theorem observe_grade (x : E) :
    queryGrade.P (Reader.observe (M := PrunedMerklePaths) hashQuery x) 1 := by
  unfold Reader.observe
  exact queryGrade.of_eq (queryGrade.bind get_grade fun st ↦ queryGrade.bind
    (lift_grade (ocGrade.map (hashQuery_grade _) _)) fun _ ↦
    modify_grade _ fun _ ↦ rfl) rfl

private theorem nextScalar_grade :
    queryGrade.P (Reader.nextScalar (M := PrunedMerklePaths) hashQuery) 1 :=
  queryGrade.of_eq (queryGrade.bind takeRaw_grade fun x ↦ queryGrade.bind (observe_grade x)
    fun _ ↦ queryGrade.pure _) rfl

private theorem sample_grade :
    queryGrade.P (Reader.sample (M := PrunedMerklePaths) hashQuery) 1 := by
  unfold Reader.sample
  exact queryGrade.of_eq (queryGrade.bind get_grade fun st ↦ queryGrade.bind
    (lift_grade (ocGrade.bind (hashQuery_grade _) fun _ ↦ ocGrade.pure _)) fun _ ↦
    queryGrade.bind (modify_grade _ fun _ ↦ rfl) fun _ ↦ queryGrade.pure _) rfl

private theorem nextRoot_grade :
    queryGrade.P (Reader.nextRoot (M := PrunedMerklePaths) hashQuery) 2 := by
  unfold Reader.nextRoot
  refine queryGrade.of_eq (queryGrade.bind nextScalar_grade fun a ↦
    queryGrade.bind (k := 0) nextScalar_grade fun b ↦ ?_) (by omega)
  split
  · exact queryGrade.pure _
  · exact throw_grade _

private theorem isTotalQueryBound_checkPow (s : FsState) (bits : ℕ) (nonce : E) :
    IsTotalQueryBound (s.checkPow hashQuery bits nonce) 3 := by
  unfold FsState.checkPow FsState.powBase FsState.powOk FsState.absorbNonce
  refine (ocGrade.bind (hashQuery_grade _) fun _ ↦
    ocGrade.ite_bind _ (ocGrade.pure _)
      (ocGrade.bind (hashQuery_grade _) fun _ ↦ ocGrade.pure _) fun _ ↦
    ocGrade.bind (ocGrade.map (hashQuery_grade _) _) fun _ ↦ ocGrade.pure _).mono ?_
  split <;> omega

private theorem checkPow_grade (bits : ℕ) :
    queryGrade.P (Reader.checkPow (M := PrunedMerklePaths) hashQuery bits) 3 := by
  unfold Reader.checkPow
  refine queryGrade.of_eq (queryGrade.bind takeRaw_grade fun nonce ↦ queryGrade.bind get_grade
    fun st ↦ queryGrade.bind (lift_grade (isTotalQueryBound_checkPow _ _ _)) fun r ↦
    queryGrade.bind (k := 0) (modify_grade _ fun _ ↦ rfl) fun _ ↦
    queryGrade.ite_of _ (queryGrade.pure _)
      (queryGrade.of_eq (queryGrade.bind (throw_grade _) fun _ ↦ queryGrade.pure _) rfl)) rfl

/-- The queries of the proof reader's primitives: a scalar one, a challenge one, a root two, a
nonce three. -/
def queryCounts : StepCounts := ⟨1, 1, 2, fun _ ↦ 3⟩

/-- **The proof reader's primitives, counted** at the random oracle. -/
theorem readerOps_graded : ChainOps.Graded queryGrade (readerOps hashQuery) queryCounts where
  nextScalar := nextScalar_grade
  sample := sample_grade
  nextRoot := nextRoot_grade
  checkPow := checkPow_grade

/-! ## The openings -/

/-- Hashing rows asks one query per row and yields one leaf per row. -/
private theorem hashRowsWith_queries (rowWords leafWords : ℕ) : ∀ rows : List (List K),
    IsTotalQueryBound (hashRowsWith hashQuery rowWords leafWords rows) rows.length ∧
      ∀ r ∈ support (hashRowsWith hashQuery rowWords leafWords rows), ∀ ds,
        r = some ds → ds.length = rows.length
  | [] => ⟨isTotalQueryBound_pure _ _, fun r hr ds hds ↦ by
      rw [hashRowsWith, mem_support_pure_iff] at hr
      subst hr
      cases hds
      rfl⟩
  | row :: rest => by
    have ih := hashRowsWith_queries rowWords leafWords rest
    rw [hashRowsWith]
    split
    · refine ⟨(isTotalQueryBound_bind (isTotalQueryBound_hashQuery _) fun _ ↦
        isTotalQueryBound_bind ih.1 fun _ ↦ isTotalQueryBound_pure _ 0).mono
          (by simp only [List.length_cons]; omega), fun r hr ds hds ↦ ?_⟩
      simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨d, -, ds', hds', rfl⟩ := hr
      cases ds' with
      | none => cases hds
      | some ds' =>
        cases hds
        simp [ih.2 _ hds' ds' rfl]
    · exact ⟨isTotalQueryBound_pure _ _, fun r hr ds hds ↦ by
        rw [mem_support_pure_iff] at hr
        subst hr
        cases hds⟩

/-- **An opening's check** asks at most a query per stored row and per row and level of the
tree. -/
theorem isTotalQueryBound_merkleVerifyWith (root : Digest) (depth rowWords leafWords : ℕ)
    (queries : List ℕ) (paths : PrunedMerklePaths) :
    IsTotalQueryBound (merkleVerifyWith hashQuery root depth rowWords leafWords queries paths)
      (paths.leafData.length * (1 + depth)) := by
  unfold merkleVerifyWith
  dsimp only
  split
  · exact isTotalQueryBound_pure _ _
  · refine (isTotalQueryBound_bind_of_mem_support
      (hashRowsWith_queries rowWords leafWords paths.leafData).1
      (suffixBound := depth * paths.leafData.length) fun r hr ↦ ?_).mono (by ring_nf; omega)
    rcases r with _ | leaves
    · exact isTotalQueryBound_pure _ _
    · simp only
      split
      · exact isTotalQueryBound_pure _ _
      · have hl := (hashRowsWith_queries rowWords leafWords paths.leafData).2 _ hr leaves rfl
        refine (isTotalQueryBound_bind (n₂ := 0) (MerkleTree.prunedRoot_queries
          (fun l r ↦ hashQuery (nodeBytes l r)) (fun _ _ ↦ isTotalQueryBound_hashQuery _) depth
          _ paths.siblingHashes) fun r ↦ ?_).mono ?_
        · rcases r with _ | r <;> exact isTotalQueryBound_pure _ _
        · simp only [List.length_zip, hl, Nat.add_zero]
          exact Nat.mul_le_mul_left _ (min_le_right _ _)

/-- Taking the next opening and checking it asks the check's queries; on success the openings
left are the rest. -/
private theorem nextOpening_queries {α : Type}
    (auth : PrunedMerklePaths → OracleComp hashSpec (Option α))
    {st : ReaderState PrunedMerklePaths} {p : PrunedMerklePaths} {ps : List PrunedMerklePaths}
    (hst : st.merkle = p :: ps) {n : ℕ} (ha : IsTotalQueryBound (auth p) n) :
    IsTotalQueryBound (runAt (Reader.nextOpening auth) st) n ∧
      ∀ r ∈ support (runAt (Reader.nextOpening auth) st), ∀ q, r = .ok q → q.2.merkle = ps := by
  unfold Reader.nextOpening
  rw [runAt_bind, show runAt (get : W _) st = pure (.ok (st, st)) from rfl, pure_bind]
  simp only [hst]
  rw [runAt_bind, show runAt (modify _ : W Unit) st = pure (.ok ((), { st with merkle := ps }))
    from rfl, pure_bind]
  simp only
  rw [runAt_bind, runAt_monadLift]
  refine ⟨(isTotalQueryBound_bind (n₂ := 0) ((isQueryBound_map_iff _ _ _ _ _).mpr ha)
    fun r ↦ ?_).mono
    (by omega), fun r hr q hq ↦ ?_⟩
  · rcases r with _ | ⟨x, s⟩
    · exact isTotalQueryBound_pure _ _
    · simp only
      split
      · exact isTotalQueryBound_pure _ _
      · exact isTotalQueryBound_pure _ _
  · simp only [mem_support_bind_iff, support_map, Set.mem_image] at hr
    obtain ⟨_, ⟨o, -, rfl⟩, hr⟩ := hr
    simp only at hr
    split at hr
    · rw [show runAt (pure _ : W α) _ = _ from runAt_pure _ _, mem_support_pure_iff] at hr
      subst hr
      cases hq
      rfl
    · rw [show runAt (throw _ : W α) _ = pure (.error _) from rfl, mem_support_pure_iff] at hr
      subst hr
      cases hq

/-- The queries of the openings of the levels `shs`: per level, a query per row and per row and
level of its tree. -/
def openingsCount : List LevelShape → ℕ
  | [] => 0
  | sh :: shs => sh.queries * (1 + (sh.msgLog + sh.rate)) + openingsCount shs

/-- **The openings** ask at most `openingsCount shs` queries when the openings left have the
shapes the setup checks. -/
theorem walkOpenings_queries (nLanes : ℕ) : ∀ (first : Bool) (root : Digest)
    (shs : List LevelShape) (ls : List WhirLevel) (st : ReaderState PrunedMerklePaths),
    openingsOk nLanes first shs st.merkle = true →
    IsTotalQueryBound (runAt (walkOpenings (readerOps hashQuery) nLanes first root shs ls) st)
      (openingsCount shs)
  | _, _, [], _, _, _ => isTotalQueryBound_pure _ _
  | _, _, _ :: _, [], _, _ => isTotalQueryBound_pure _ _
  | first, root, sh :: shs, l :: ls, st, hok => by
    obtain ⟨p, ps, hst⟩ : ∃ p ps, st.merkle = p :: ps := by
      rcases h : st.merkle with _ | ⟨p, ps⟩
      · rw [h] at hok
        simp [openingsOk] at hok
      · exact ⟨p, ps, rfl⟩
    rw [hst, openingsOk] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hq, -⟩, -⟩, hrest⟩ := hok
    have h₁ := nextOpening_queries (merkleVerifyWith hashQuery root (sh.msgLog + sh.rate)
      (rowWordsOf nLanes first sh) (leafWordsOf first sh) l.positions) hst
      (isTotalQueryBound_merkleVerifyWith _ _ _ _ _ _)
    rw [walkOpenings, runAt_bind]
    refine (isTotalQueryBound_bind_of_mem_support h₁.1 (suffixBound := openingsCount shs)
      fun r hr ↦ ?_).mono ?_
    · rcases r with _ | ⟨rows, st'⟩
      · exact isTotalQueryBound_pure _ _
      · simp only
        rw [runAt_bind]
        refine (isTotalQueryBound_bind (n₂ := 0)
          (walkOpenings_queries nLanes false _ shs ls st' ?_) fun r ↦ ?_).mono (by omega)
        · rw [h₁.2 _ hr _ rfl]
          exact hrest
        · rcases r with _ | ⟨rest, st''⟩ <;> exact isTotalQueryBound_pure _ _
    · simp only [openingsCount]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hq) _

/-! ## The verifier -/

private theorem finish_grade : queryGrade.P (Reader.finish (m := OracleComp hashSpec)
    (M := PrunedMerklePaths)) 0 := by
  unfold Reader.finish
  exact queryGrade.bind (k := 0) get_grade fun _ ↦
    queryGrade.ite_of _ (queryGrade.pure _) (throw_grade _)

/-- The queries of the verifier at the sizes `s` and the opening's levels `shs`: the chain walk's
and the openings'. -/
def queryCount (prog : Program) (input : PublicInput) (s : Sizes) (shs : List LevelShape) : ℕ :=
  queryCounts.chain prog s input shs + openingsCount shs

/-- The walk and the openings, then the check that the proof is consumed, ask at most
`queryCount` queries from a state whose openings have the levels' shapes. -/
private theorem isTotalQueryBound_walk (prog : Program) (s : Sizes) (input : PublicInput)
    (shs : List LevelShape) (st : ReaderState PrunedMerklePaths)
    (hok : openingsOk (nLanes prog s) true shs st.merkle = true) :
    IsTotalQueryBound (runAt (do
        let x ← walkProof (readerOps hashQuery) prog s input shs
        Reader.finish
        return x : W (Wire × List (List (List K)))) st) (queryCount prog input s shs) := by
  have hc := walkChain_grade readerOps_graded prog s input shs st
  simp only [walkProof, bind_assoc, pure_bind]
  rw [runAt_bind]
  refine isTotalQueryBound_bind_of_mem_support hc.1 fun r hr ↦ ?_
  rcases r with _ | ⟨w, st'⟩
  · exact isTotalQueryBound_pure _ _
  · simp only
    rw [runAt_bind]
    refine (isTotalQueryBound_bind (n₂ := 0) (walkOpenings_queries _ _ _ shs _ st'
      (by rw [hc.2 _ hr _ rfl]; exact hok)) fun r ↦ ?_).mono (by omega)
    rcases r with _ | ⟨rows, st''⟩
    · exact isTotalQueryBound_pure _ _
    · exact ((queryGrade.bind (k := 0) finish_grade fun _ ↦ queryGrade.pure _) st'').1

/-- **The verifier at the random oracle**, on a proof announcing the sizes `s` and the rate `ρ`
whose ladder has the levels `levels`, asks at most `queryCount` queries at those sizes and
levels. -/
theorem isTotalQueryBound_verifyWith {prog : Program} {input : PublicInput}
    {proof : Proof PrunedMerklePaths} {s : Sizes} {ρ : ℕ} {levels : List Whir.Level}
    (hs : setup? prog proof = some (s, ρ)) (hl : ladderOf prog s ρ = some levels) :
    IsTotalQueryBound (verifyWith hashQuery prog input proof)
      (queryCount prog input s (levelShapes (stackMu prog s) levels)) := by
  unfold verifyWith
  rw [hs]
  simp only [hl]
  split
  · exact isTotalQueryBound_pure _ _
  · rename_i hok
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hok
    refine (isTotalQueryBound_bind
      (n₁ := queryCount prog input s (levelShapes (stackMu prog s) levels))
      (n₂ := 0) ?_ fun r ↦ ?_).mono (by omega)
    · rw [StateT.run'_eq, ExceptT.run_map]
      exact (isQueryBound_map_iff _ _ _ _ _).mpr
        (isTotalQueryBound_walk prog s input _ ⟨FsState.seed prog input, proof.stream,
          proof.merkle⟩ hok)
    · rcases r with _ | ⟨w, rows⟩ <;> exact isTotalQueryBound_pure _ _

/-! ## The maximum over the admissible sizes -/

/-- The verifier's queries at the sizes `s` and the rate `ρ`: at the ladder's levels, `0` when
there is no ladder (the verifier then asks none). -/
def queryCountAt (prog : Program) (input : PublicInput) (s : Sizes) (ρ : ℕ) : ℕ :=
  match ladderOf prog s ρ with
  | none => 0
  | some levels => queryCount prog input s (levelShapes (stackMu prog s) levels)

/-- The box the admissible announcements lie in: the memory's log-size, the six tables'
log-heights and the rate. Irreducible: a unification that unfolds it would enumerate it. -/
@[irreducible] def sizesBox : Finset (ℕ × (Fin 6 → Fin (maxLogRows + 1)) × ℕ) :=
  Finset.range (maxLogMem + 1) ×ˢ Finset.univ ×ˢ Finset.range 5

/-- The queries at a point of the box, `0` off the sizes. -/
def queryCountOf (prog : Program) (input : PublicInput)
    (p : ℕ × (Fin 6 → Fin (maxLogRows + 1)) × ℕ) : ℕ :=
  if h : 0 < p.1 then queryCountAt prog input ⟨p.1, h, fun j ↦ p.2.1 j⟩ p.2.2 else 0

/-- **The verifier's queries**, maximised over the admissible sizes and rates. -/
def verifierQueries (prog : Program) (input : PublicInput) : ℕ :=
  sizesBox.sup (queryCountOf prog input)

/-- The sizes and rate the setup accepts pass its checks. -/
theorem setupOk_of_setup {prog : Program} {proof : Proof PrunedMerklePaths} {s : Sizes} {ρ : ℕ}
    (h : setup? prog proof = some (s, ρ)) : setupOk prog s ρ = true := by
  unfold setup? at h
  split at h
  · split at h
    · cases h
      assumption
    · cases h
  · cases h

/-- The queries at admissible sizes and a valid rate are at most the maximum. -/
private theorem queryCountAt_le {prog : Program} {input : PublicInput} {s : Sizes} {ρ : ℕ}
    (h : setupOk prog s ρ = true) : queryCountAt prog input s ρ ≤ verifierQueries prog input := by
  simp only [setupOk, decide_eq_true_eq] at h
  obtain ⟨⟨-, hmem, hτ, -, -⟩, -, hρ⟩ := h
  have hmem' : (⟨s.logMem, fun j ↦ ⟨s.τ j, Nat.lt_succ_of_le (hτ j)⟩, ρ⟩ :
      ℕ × (Fin 6 → Fin (maxLogRows + 1)) × ℕ) ∈ sizesBox := by
    unfold sizesBox
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, true_and]
    exact ⟨Nat.lt_succ_of_le hmem, by omega⟩
  have key : ∀ p ∈ sizesBox, queryCountOf prog input p ≤ verifierQueries prog input :=
    fun _ hp ↦ Finset.le_sup hp
  have hle := key _ hmem'
  have heq : queryCountOf prog input ⟨s.logMem, fun j ↦ ⟨s.τ j, Nat.lt_succ_of_le (hτ j)⟩, ρ⟩ =
      queryCountAt prog input s ρ := by
    simp only [queryCountOf, s.logMem_pos, ↓reduceDIte]
  rw [heq] at hle
  exact hle

/-- **The verifier's queries are bounded**: on every proof, the verifier at the random oracle asks
at most `verifierQueries prog input` queries. The sizes, the rate and the openings' shapes are
checked before the first hash. -/
theorem verifierQueries_bound (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) :
    IsTotalQueryBound (verifyWith hashQuery prog input proof) (verifierQueries prog input) := by
  rcases hs : setup? prog proof with _ | ⟨s, ρ⟩
  · rw [verifyWith_of_setup _ hs]
    exact isTotalQueryBound_pure _ _
  rcases hl : ladderOf prog s ρ with _ | levels
  · unfold verifyWith
    rw [hs]
    simp only [hl]
    exact isTotalQueryBound_pure _ _
  refine (isTotalQueryBound_verifyWith hs hl).mono ?_
  have h := queryCountAt_le (input := input) (setupOk_of_setup hs)
  simp only [queryCountAt, hl] at h
  exact h

end VerifierQueries

end

end LeanerVM.Protocol
