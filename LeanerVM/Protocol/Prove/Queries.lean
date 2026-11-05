/-
  LeanerVM.Protocol.Prove.Queries

  The honest prover's hash queries at the random oracle, bounded in closed form in the sizes and
  the fuel, and numerically over the admissible sizes.
-/

module

public import LeanerVM.Protocol.Prove.Hom
public import LeanerVM.Protocol.ToArkLib.RunCodecGrade
public import LeanerVM.Protocol.LeanVmReader
public import LeanerVM.Protocol.Compile.Agree

/-!
# The prover's queries

`Prove.queryGrade` is the property of a computation of the prover at the random oracle,
`ProveM (OracleComp hashSpec)`, that every run of it from any book and writer state asks at most
`k` queries (`IsTotalQueryBound`). The writer's primitives have their counts: a scalar sent one
query, a challenge one, a grind `fuel + 2` (the base, at most `fuel` candidates, the absorption),
a commitment to `2 ^ d` rows `2 ^ (d + 1) + 2` (the leaves, the tree, the root sent).

Each phase's wire is counted round by round (`RoundCodec.GradedOn`): the bus phase, the table
sumcheck, the public input and the Flock phase at the verifier's counts
(`VerifierQueries.queryCounts`), WHIR's levels at the verifier's counts with each commitment's
tree and each grind's candidates (`ladderQueries`). The public input's message is a list; it is
counted on the honest transcripts, whose message has one value per sent line, as the compiled
protocol's perfect completeness and the verifiers' agreement give (`writeProof_grade`).
`isTotalQueryBound_proveWith`: the prover asks at most the seed's three, the announcement's eight
and the wire's `wireQueries`. Over the window of WHIR's parameters (one decision,
`window_key`) and the admissible sizes, that is at most `264246250 + 6 · fuel`
(`isTotalQueryBound_proveWith_closed`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization Blake2sHash LeanIsa Whir
open OracleComp OracleSpec ProtocolSpec StepSchedule
open Air.Flat (EnsembleWitness)

@[expose] public section

namespace Prove

/-- The prover's monad at the random oracle. -/
abbrev QM : Type → Type := ProveM (OracleComp hashSpec)

/-- A run of the prover's monad from a book and a writer state, as an oracle computation. -/
abbrev runQ {α : Type} (a : QM α) (b : Book) (ws : WriterState PrunedMerklePaths) :
    OracleComp hashSpec (Option ((α × Book) × WriterState PrunedMerklePaths)) :=
  ((a.run b).run ws).run

theorem runQ_bind {α β : Type} (a : QM α) (f : α → QM β) (b : Book)
    (ws : WriterState PrunedMerklePaths) :
    runQ (a >>= f) b ws = runQ a b ws >>= fun o ↦ match o with
      | some p => runQ (f p.1.1) p.1.2 p.2
      | none => pure none := by
  simp only [runQ, StateT.run_bind, OptionT.run_bind, Option.elimM]
  congr 1
  funext o
  rcases o with _ | ⟨⟨x, b'⟩, ws'⟩ <;> rfl

/-- A hash is one query. -/
theorem isTotalQueryBound_hashQuery' (t : List UInt8) : IsTotalQueryBound (hashQuery t) 1 := by
  have h := (isTotalQueryBound_query_bind_iff (spec := hashSpec) (t := t)
    (mx := (pure : Digest → OracleComp hashSpec Digest)) (n := 1)).mpr
    ⟨Nat.one_pos, fun u ↦ isQueryBound_pure u 0 _ _⟩
  rwa [bind_pure] at h

theorem itqb_pure {α : Type} (x : α) (n : ℕ) :
    IsTotalQueryBound (pure x : OracleComp hashSpec α) n :=
  isQueryBound_pure x n _ _

/-- Oracle computations of at most `n` queries. -/
def ocGrade : MonadGrade (OracleComp hashSpec) where
  P c n := IsTotalQueryBound c n
  pure x := isQueryBound_pure x 0 _ _
  bind ha hf := isTotalQueryBound_bind ha hf

/-- **The prover's computations of at most `k` queries** on every run, from every book and
writer state. -/
def queryGrade : MonadGrade QM where
  P a k := ∀ b ws, IsTotalQueryBound (runQ a b ws) k
  pure _ _ _ := isQueryBound_pure _ 0 _ _
  bind ha hf b ws := by
    rw [runQ_bind]
    exact isTotalQueryBound_bind (ha b ws) fun o ↦ match o with
      | some p => hf p.1.1 p.1.2 p.2
      | none => isQueryBound_pure _ _ _ _

theorem queryGrade_mono {α : Type} {a : QM α} {k k' : ℕ} (h : queryGrade.P a k) (hk : k ≤ k') :
    queryGrade.P a k' := fun b ws ↦ (h b ws).mono hk

theorem queryGrade_of_map {α β : Type} (f : α → β) (a : QM α) (k : ℕ)
    (h : queryGrade.P (f <$> a) k) : queryGrade.P a k := fun b ws ↦ by
  have hmap : runQ (f <$> a) b ws = (fun o ↦ match o with
      | some p => some ((f p.1.1, p.1.2), p.2)
      | none => none) <$> runQ a b ws := by
    rw [← bind_pure_comp, runQ_bind, map_eq_bind_pure_comp]
    congr 1
    funext o
    rcases o with _ | ⟨⟨x, b'⟩, ws'⟩ <;> rfl
  have := h b ws
  rw [hmap] at this
  exact (isQueryBound_map_iff _ _ _ _ _).mp this

/-! ## The primitives -/

/-- An oracle computation lifted to the prover. -/
theorem queryGrade_liftM {α : Type} {c : OracleComp hashSpec α} {k : ℕ}
    (hc : IsTotalQueryBound c k) : queryGrade.P (liftM c : QM α) k := fun b ws ↦ by
  have : runQ (liftM c : QM α) b ws = (fun x ↦ some ((x, b), ws)) <$> c := by
    simp only [runQ, liftM, monadLift, MonadLift.monadLift, StateT.run_lift, OptionT.lift,
      OptionT.mk, StateT.run_bind, OptionT.run_bind]
    simp [Option.elimM, map_eq_bind_pure_comp, OptionT.run, bind_assoc]
    congr 1
  rw [this]
  exact (isQueryBound_map_iff _ _ _ _ _).mpr hc

/-- A writer's computation lifted to the prover. -/
theorem queryGrade_lift {α : Type} {y : WriteM (OracleComp hashSpec) PrunedMerklePaths α} {k : ℕ}
    (hy : ∀ ws, IsTotalQueryBound (y.run ws).run k) : queryGrade.P (StateT.lift y : QM α) k :=
  fun b ws ↦ by
  have : runQ (StateT.lift y : QM α) b ws =
      (Option.map fun p ↦ ((p.1, b), p.2)) <$> (y.run ws).run := by
    simp only [runQ, StateT.run_lift, StateT.run_bind, OptionT.run_bind]
    simp only [Option.elimM, map_eq_bind_pure_comp]
    congr 1
    funext o
    rcases o with _ | ⟨x, ws'⟩ <;> rfl
  rw [this]
  exact (isQueryBound_map_iff _ _ _ _ _).mpr (hy ws)

theorem queryGrade_modify (f : Book → Book) : queryGrade.P (modify f : QM Unit) 0 :=
  fun _ _ ↦ isQueryBound_pure _ _ _ _

theorem queryGrade_get : queryGrade.P (get : QM Book) 0 :=
  fun _ _ ↦ isQueryBound_pure _ _ _ _

theorem queryGrade_failure {α : Type} : queryGrade.P (failure : QM α) 0 :=
  fun _ _ ↦ by
  simp only [runQ]
  simp
  exact itqb_pure _ _

section Writer

variable (fuel : ℕ) {M : Type}

theorem addScalar_queries (x : E) (ws : WriterState M) :
    IsTotalQueryBound ((Writer.addScalar hashQuery x).run ws).run 1 := by
  simp [Writer.addScalar, FsState.observe, hashQuery]
  exact (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_hashQuery' _)

theorem addScalars_queries : ∀ (xs : List E) (ws : WriterState M),
    IsTotalQueryBound ((Writer.addScalars hashQuery xs).run ws).run xs.length
  | [], _ => isQueryBound_pure _ _ _ _
  | x :: xs, ws => by
    simp only [Writer.addScalars, StateT.run_bind, OptionT.run_bind, Option.elimM]
    refine (isTotalQueryBound_bind (n₁ := 1) (n₂ := xs.length) (addScalar_queries x ws)
      fun o ↦ ?_).mono (by simp only [List.length_cons]; omega)
    rcases o with _ | ⟨u, ws'⟩
    · exact itqb_pure _ _
    · exact addScalars_queries xs ws'

theorem sample_queries (ws : WriterState M) :
    IsTotalQueryBound ((Writer.sample hashQuery).run ws).run 1 := by
  simp [Writer.sample, FsState.sample, hashQuery]
  exact (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_hashQuery' _)

theorem findNonce_queries (base : Digest) (bits : ℕ) :
    ∀ f n, IsTotalQueryBound (FsState.findNonce hashQuery base bits f n) f
  | 0, _ => itqb_pure _ _
  | f + 1, n => by
    unfold FsState.findNonce FsState.powOk
    refine (isTotalQueryBound_bind (n₁ := 1) (n₂ := f) (isTotalQueryBound_bind (n₁ := 1)
      (n₂ := 0) (isTotalQueryBound_hashQuery' _) fun _ ↦ itqb_pure _ _) fun ok ↦ ?_).mono
      (by omega)
    split
    · exact itqb_pure _ _
    · exact findNonce_queries base bits f (n + 1)

theorem fsGrind_queries (s : FsState) (bits : ℕ) :
    IsTotalQueryBound (s.grind hashQuery fuel bits) (fuel + 2) := by
  unfold FsState.grind FsState.powBase FsState.absorbNonce
  rw [show fuel + 2 = 1 + (fuel + 1) by omega]
  refine isTotalQueryBound_bind (isTotalQueryBound_hashQuery' _) fun base ↦ ?_
  have habs : ∀ n, IsTotalQueryBound (do
      let fs ← FsState.mk <$> hashQuery (FsState.stepBytes s.cv (FsState.nonceOf n)
        FsState.powNonceTag)
      pure (some (FsState.nonceOf n, fs)) : OracleComp hashSpec (Option (E × FsState))) 1 :=
    fun n ↦ isTotalQueryBound_bind (n₂ := 0)
      ((isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_hashQuery' _))
      fun _ ↦ itqb_pure _ _
  dsimp only
  split
  · rw [pure_bind]
    exact (habs 0).mono (by omega)
  · refine isTotalQueryBound_bind (n₁ := fuel) (n₂ := 1) (findNonce_queries _ _ _ _) fun n? ↦ ?_
    rcases n? with _ | n
    · exact itqb_pure _ _
    · exact habs n

theorem grind_queries (bits : ℕ) (ws : WriterState M) :
    IsTotalQueryBound ((Writer.grind hashQuery fuel bits).run ws).run (fuel + 2) := by
  simp [Writer.grind]
  refine (isTotalQueryBound_bind (n₂ := 0) (fsGrind_queries fuel ws.fs bits) fun o ↦ ?_).mono
    (by omega)
  rcases o with _ | p
  · simp
    exact itqb_pure _ _
  · exact itqb_pure _ _

end Writer

/-! ## The Merkle commitment -/

theorem list_mapM_queries {α β : Type} (f : α → OracleComp hashSpec β) (k : ℕ)
    (hf : ∀ x, IsTotalQueryBound (f x) k) :
    ∀ l : List α, IsTotalQueryBound (l.mapM f) (l.length * k)
  | [] => itqb_pure _ _
  | x :: l => by
    rw [List.mapM_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact isTotalQueryBound_bind (hf x) fun _ ↦ isTotalQueryBound_bind (n₂ := 0)
      (list_mapM_queries f k hf l) fun _ ↦ itqb_pure _ _

theorem vector_mapM_queries {α β : Type} {n : ℕ} (f : α → OracleComp hashSpec β) (k : ℕ)
    (hf : ∀ x, IsTotalQueryBound (f x) k) (v : Vector α n) :
    IsTotalQueryBound (v.mapM f) (n * k) := by
  have h : IsTotalQueryBound (Vector.toArray <$> v.mapM f) (n * k) := by
    rw [Vector.toArray_mapM, Array.mapM_eq_mapM_toList]
    refine (isQueryBound_map_iff _ _ _ _ _).mpr ?_
    have := list_mapM_queries f k hf v.toArray.toList
    rw [Array.length_toList, Vector.size_toArray] at this
    exact this
  exact (isQueryBound_map_iff _ _ _ _ _).mp h

theorem parentsM_queries {k : ℕ} (level : Vector Digest (2 ^ (k + 1))) :
    IsTotalQueryBound (MerkleTree.parentsM (fun l r ↦ hashQuery (nodeBytes l r)) level)
      (2 ^ k) := by
  unfold MerkleTree.parentsM
  simpa using vector_mapM_queries _ 1 (fun _ ↦ isTotalQueryBound_hashQuery' _) _

theorem buildLevelsM_queries :
    ∀ (k : ℕ) (level : Vector Digest (2 ^ k)),
      IsTotalQueryBound (MerkleTree.buildLevelsM (fun l r ↦ hashQuery (nodeBytes l r)) k level)
        (2 ^ k)
  | 0, _ => itqb_pure _ _
  | k + 1, level => by
    unfold MerkleTree.buildLevelsM
    rw [pow_succ, Nat.mul_two]
    exact isTotalQueryBound_bind (parentsM_queries level) fun ps ↦
      isTotalQueryBound_bind (n₂ := 0) (buildLevelsM_queries k ps) fun _ ↦ itqb_pure _ _

theorem merkleCommitWithM_queries (leafWords : ℕ) {d : ℕ} (rows : Vector (List K) (2 ^ d)) :
    IsTotalQueryBound (merkleCommitWithM hashQuery leafWords rows) (2 ^ d + 2 ^ d) := by
  unfold merkleCommitWithM
  refine isTotalQueryBound_bind (vector_mapM_queries _ 1 (fun _ ↦ isTotalQueryBound_hashQuery' _)
    rows |>.mono (by omega)) fun leaves ↦ ?_
  exact isTotalQueryBound_bind (n₂ := 0) (buildLevelsM_queries d leaves) fun _ ↦ itqb_pure _ _

/-! ## The writer's primitives at the oracle -/

section Ops

variable (fuel : ℕ)

/-- The writer's primitives at the random oracle. -/
abbrev qops : WireOps QM := proveOps hashQuery fuel

theorem send_grade (x : E) : queryGrade.P ((qops fuel).send x) 1 :=
  queryGrade_lift (addScalar_queries x)

theorem sample_grade : queryGrade.P (qops fuel).sample 1 :=
  queryGrade_lift (sample_queries)

theorem grind_grade : queryGrade.P (qops fuel).grind (fuel + 2) :=
  queryGrade_lift (grind_queries fuel queryGrindingBits)

theorem commit_grade (depth leafWords : ℕ) (rows : Vector (List K) (2 ^ depth)) :
    queryGrade.P ((qops fuel).commit depth leafWords rows) (2 ^ (depth + 1) + 2) := by
  refine queryGrade.of_eq (queryGrade.bind
    (queryGrade_liftM (merkleCommitWithM_queries leafWords rows)) fun c ↦
    queryGrade.bind (queryGrade_modify _) fun _ ↦
      queryGrade_lift (k := 2) (addScalars_queries [_, _])) ?_
  simp [pow_succ]
  omega

theorem record_grade (ps : List ℕ) : queryGrade.P ((qops fuel).record ps) 0 :=
  queryGrade_modify _

theorem commit_le {depth D : ℕ} (hd : depth ≤ D) {leafWords : ℕ}
    {rows : Vector (List K) (2 ^ depth)} :
    queryGrade.P ((qops fuel).commit depth leafWords rows) (2 ^ (D + 1) + 2) :=
  queryGrade_mono (commit_grade fuel depth leafWords rows)
    (by have := Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.succ_le_succ hd); omega)

theorem sendAll_grade : ∀ xs : List E, queryGrade.P (sendAll (qops fuel) xs) xs.length
  | [] => queryGrade.pure _
  | x :: xs => queryGrade.of_eq (queryGrade.bind (send_grade fuel x) fun _ ↦
      sendAll_grade xs) (by simp [Nat.add_comm])

theorem samples_grade : ∀ k, queryGrade.P (samples (qops fuel) k) k
  | 0 => queryGrade.pure _
  | k + 1 => queryGrade.of_eq (queryGrade.bind (sample_grade fuel) fun _ ↦
      queryGrade.bind (samples_grade k) fun _ ↦ queryGrade.pure _) (by omega)

theorem positionsWith_grade (depth : ℕ) : ∀ f need,
    queryGrade.P (Verify.positionsWith (qops fuel).sample depth f need)
      (VerifierQueries.queryCounts.positions depth f need)
  | 0, _ => queryGrade.pure _
  | _ + 1, 0 => queryGrade.pure _
  | f + 1, _ + 1 => queryGrade.of_eq (queryGrade.bind (sample_grade fuel) fun _ ↦
      queryGrade.bind (positionsWith_grade depth f _) fun _ ↦ queryGrade.pure _)
      (by simp [Verify.StepCounts.positions, VerifierQueries.queryCounts])

theorem positions_grade (depth t : ℕ) :
    queryGrade.P (positions (qops fuel) depth t)
      (VerifierQueries.queryCounts.positions depth t t) :=
  queryGrade.of_eq (queryGrade.bind (positionsWith_grade fuel depth t t) fun ps ↦
    queryGrade.bind (record_grade fuel ps) fun _ ↦ queryGrade.pure _) (by omega)

theorem sendPlain_grade {d : ℕ} (hd : 0 < d) (c : Vector E (d + 1)) :
    queryGrade.P (sendPlain (qops fuel) c) d := by
  have := sendAll_grade fuel (RoundPoly.encode none c)
  rwa [RoundPoly.length_encode hd] at this

theorem sendNormal_grade {d : ℕ} (hd : 0 < d) (c : Vector E (d + 1)) :
    queryGrade.P (sendNormal (qops fuel) c) d := by
  have := sendAll_grade fuel (RoundPoly.encode (some 0) c)
  rwa [RoundPoly.length_encode hd] at this

theorem sendTables_grade {k ρ : ℕ} (c : Fin k → Vector E (2 ^ ρ)) :
    queryGrade.P (sendTables (qops fuel) c) (k * 2 ^ ρ) := by
  have := sendAll_grade fuel ((List.finRange k).flatMap fun t ↦ (c t).toList)
  rw [List.length_flatMap] at this
  simp only [Vector.length_toList, List.map_const', List.length_finRange, List.sum_replicate,
    smul_eq_mul] at this
  exact this

theorem sendVec_grade {k : ℕ} (v : Vector E k) :
    queryGrade.P (sendAll (qops fuel) v.toList) k := by
  have := sendAll_grade fuel v.toList
  rwa [Vector.length_toList] at this

/-! ## The phases' wires -/

open RoundCodec

/-- The verifier's counts at the random oracle: a scalar, a challenge one query. -/
abbrev qc : Verify.StepCounts := VerifierQueries.queryCounts

/-- Two wires in sequence, counted on every transcript. -/
theorem gapp {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n} {c₁ : RoundCodec QM p₁}
    {c₂ : RoundCodec QM p₂} {k₁ k₂ : ℕ} (h₁ : c₁.GradedOn queryGrade (fun _ ↦ True) k₁)
    (h₂ : c₂.GradedOn queryGrade (fun _ ↦ True) k₂) :
    (c₁.append c₂).GradedOn queryGrade (fun _ ↦ True) (k₁ + k₂) :=
  (h₁.append h₂).mono (fun _ _ ↦ ⟨trivial, trivial⟩) le_rfl

theorem step_graded (ρ m : ℕ) :
    (RoundCodec.step (nside := 3) ρ m (sendNormal (qops fuel)) (sendTables (qops fuel))
      (qops fuel).sample).GradedOn queryGrade (fun _ ↦ True) (qc.layer ρ m) :=
  (gapp (gapp (gapp (gradedOn_chal (sample_grade fuel))
    (gradedOn_rounds (sendNormal_grade fuel (Nat.two_pow_pos ρ)) (sample_grade fuel) m))
    (gradedOn_msg (sendTables_grade fuel))) (gradedOn_chals (sample_grade fuel) ρ)).mono
    (fun _ _ ↦ trivial) (by
      simp only [Verify.StepCounts.layer, Verify.StepCounts.rounds, Verify.StepCounts.round,
        VerifierQueries.queryCounts]
      ring_nf
      omega)

theorem steps_graded : ∀ k m,
    (RoundCodec.steps (nside := 3) (sendNormal (qops fuel)) (sendTables (qops fuel))
      (qops fuel).sample k m).GradedOn queryGrade (fun _ ↦ True)
      (qc.layers (List.replicate k 2) m)
  | 0, _ => gradedOn_empty.mono (fun _ _ ↦ trivial) (Nat.zero_le _)
  | k + 1, m => (gapp (step_graded fuel 2 m) (steps_graded k (m + 2))).mono (fun _ _ ↦ trivial)
      (by simp [List.replicate_succ, Verify.StepCounts.layers])

theorem odd_graded : ∀ r,
    (RoundCodec.odd (nside := 3) (sendNormal (qops fuel)) (sendTables (qops fuel))
      (qops fuel).sample r).GradedOn queryGrade (fun _ ↦ True)
      (if r = 0 then 0 else qc.layer 1 0)
  | 0 => gradedOn_empty.mono (fun _ _ ↦ trivial) (Nat.zero_le _)
  | r + 1 => (step_graded fuel 1 0).mono (fun _ _ ↦ trivial) (by simp)

theorem gkr_graded (μ : ℕ) :
    (RoundCodec.gkr (nside := 3) μ (sendNormal (qops fuel)) (sendTables (qops fuel))
      (sendNormal (qops fuel)) (sendTables (qops fuel)) (qops fuel).sample).GradedOn queryGrade
      (fun _ ↦ True) (qc.layers (Verify.gkrRadices μ) 0 + 1) :=
  (gapp (gapp (odd_graded fuel (μ % 2)) (steps_graded fuel (μ / 2) (μ % 2)))
    (gradedOn_chal (sample_grade fuel))).mono (fun _ _ ↦ trivial) (by
      rcases Nat.mod_two_eq_zero_or_one μ with h | h <;>
        simp [Verify.gkrRadices, h, Verify.StepCounts.layers])

theorem busCodec_graded (I : M3Instance) :
    (busCodec (qops fuel) I).GradedOn queryGrade (fun _ ↦ True) (qc.bus I.μBus I.busClaims) :=
  (gapp (gapp (gapp (gradedOn_chal (queryGrade.of_eq (queryGrade.bind (samples_grade fuel 4)
      fun _ ↦ queryGrade.bind (sample_grade fuel) fun _ ↦ queryGrade.pure _) rfl))
    (gradedOn_msg fun _ ↦ queryGrade.bind (send_grade fuel _) fun _ ↦ send_grade fuel _))
    (gkr_graded fuel I.μBus)) (gradedOn_msg (sendVec_grade fuel))).mono (fun _ _ ↦ trivial)
    (by simp only [Verify.StepCounts.bus, VerifierQueries.queryCounts]; omega)

theorem tableCodec_graded (I : M3Instance) :
    (tableCodec (qops fuel) I).GradedOn queryGrade (fun _ ↦ True)
      (qc.tables I.τmax I.tableColumns) :=
  (gapp (gapp (gradedOn_chal (sample_grade fuel))
    (gradedOn_rounds (sendPlain_grade fuel (by norm_num)) (sample_grade fuel) I.τmax))
    (gradedOn_msg (sendVec_grade fuel))).mono (fun _ _ ↦ trivial)
    (by simp only [Verify.StepCounts.tables, Verify.StepCounts.rounds, Verify.StepCounts.round,
      VerifierQueries.queryCounts]; omega)

theorem pubCodec_graded (n : ℕ) :
    (pubCodec (qops fuel)).GradedOn queryGrade (fun tr ↦ (tr 1).length = n) (qc.pub n) :=
  ⟨![1, n], by simp [Verify.StepCounts.pub, VerifierQueries.queryCounts, Nat.add_comm],
    fun tr htr i h ↦ (match i, h with
      | ⟨0, _⟩, h => nomatch h
      | ⟨1, _⟩, _ => by
        show queryGrade.P (sendAll (qops fuel) (tr 1)) n
        rw [← htr]
        exact sendAll_grade fuel _),
    fun i h ↦ match i, h with
      | ⟨0, _⟩, _ => sample_grade fuel
      | ⟨1, _⟩, h => nomatch h⟩

theorem flockCodecOf_graded (k : ℕ) :
    (flockCodecOf (qops fuel) k).GradedOn queryGrade (fun _ ↦ True) (qc.flock k) :=
  (gapp (gapp (gapp (gapp (gapp (gapp (gapp (gapp (gapp
    (gradedOn_chals (sample_grade fuel) (k + 1)) (gradedOn_msg (sendVec_grade fuel)))
    (gradedOn_chal (sample_grade fuel)))
    (gradedOn_rounds (sendNormal_grade fuel (by norm_num)) (sample_grade fuel) 8))
    (gradedOn_rounds (sendNormal_grade fuel (by norm_num)) (sample_grade fuel) k))
    (gradedOn_msg (sendVec_grade fuel))) (gradedOn_chal (sample_grade fuel)))
    (gradedOn_rounds (sendPlain_grade fuel (by norm_num)) (sample_grade fuel) 8))
    (gradedOn_msg (sendVec_grade fuel))) (gradedOn_chals (sample_grade fuel) 6)).mono
    (fun _ _ ↦ trivial) (by
      simp only [Verify.StepCounts.flock, Verify.StepCounts.rounds, Verify.StepCounts.round,
        VerifierQueries.queryCounts, Flock.kSkip, Flock.kIn]
      omega)

/-! ## WHIR's levels -/

/-- The prover's counts when every commitment has at most `2 ^ D` positions: a scalar and a
challenge one query each, a commitment `2 ^ (D + 1) + 2` (its leaves, its tree and its root sent),
a grind `fuel + 2` (the base, the candidates and the absorption). -/
def proverCounts (D : ℕ) : Verify.StepCounts := ⟨1, 1, 2 ^ (D + 1) + 2, fun _ ↦ fuel + 2⟩

theorem positions_counts (c c' : Verify.StepCounts) (h : c.sample = c'.sample) (depth : ℕ) :
    ∀ f need, c.positions depth f need = c'.positions depth f need
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | f + 1, need + 1 => by
    simp only [Verify.StepCounts.positions, h, positions_counts c c' h depth f]

theorem tail_eq (c : Verify.StepCounts) (hs : c.sample = 1) (hc : c.scalar = 1) :
    ∀ k, c.tail (k + 1) = 3 * k + 1
  | 0 => by simp [Verify.StepCounts.tail, hs]
  | k + 1 => by
    rw [Verify.StepCounts.tail, tail_eq c hs hc k]
    simp [hs, hc]
    omega

theorem finalCodec_graded (sh : Whir.Shape) (nf D : ℕ) :
    (finalCodec (qops fuel) sh nf).GradedOn queryGrade (fun _ ↦ True)
      ((proverCounts fuel D).level ⟨sh.ℓ, nf + 1, sh.R, sh.t, true⟩) :=
  (gapp (gradedOn_chal (sample_grade fuel)) <|
    gapp (gradedOn_rounds (sendPlain_grade fuel (by norm_num)) (sample_grade fuel) sh.lm1) <|
    gapp (gradedOn_msg (sendPlain_grade fuel (by norm_num))) <|
    gapp (gradedOn_msg fun _ ↦ sendVec_grade fuel _) <|
    gapp (gradedOn_msg fun _ ↦ grind_grade fuel) <|
    gapp (gradedOn_chal (positions_grade fuel _ _)) <|
    gapp (gradedOn_chal (sample_grade fuel)) <|
    gapp gradedOn_empty <|
    gapp (gradedOn_msg (sendPlain_grade fuel (by norm_num))) <|
    gapp gradedOn_empty <|
    gapp (gradedOn_chal (sample_grade fuel)) <|
    gapp (gradedOn_rounds (sendPlain_grade fuel (by norm_num)) (sample_grade fuel) nf)
      gradedOn_empty).mono (fun _ _ ↦ trivial) (by
      have hp := positions_counts (proverCounts fuel D) VerifierQueries.queryCounts rfl
        (nf + 1 + sh.R) sh.t sh.t
      have ht := tail_eq (proverCounts fuel D) rfl rfl nf
      simp only [Verify.StepCounts.level, Verify.StepCounts.folds, ite_true]
      rw [hp, ht]
      simp only [proverCounts, Whir.Shape.ℓ]
      omega)

theorem levelCodec_graded (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step}
    {rest : RoundCodec QM (seqSpec k)} {krest D : ℕ}
    (hrest : rest.GradedOn queryGrade (fun _ ↦ True) krest) (hD : κ' + sh'.R ≤ D) :
    (levelCodec (qops fuel) sh sh' κ' rest).GradedOn queryGrade (fun _ ↦ True)
      ((proverCounts fuel D).level ⟨sh.ℓ, Kap sh' κ', sh.R, sh.t, false⟩ + krest) :=
  (gapp (gradedOn_chal (sample_grade fuel)) <|
    gapp (gradedOn_rounds (sendPlain_grade fuel (by norm_num)) (sample_grade fuel) sh.lm1) <|
    gapp (gradedOn_msg (sendPlain_grade fuel (by norm_num))) <|
    gapp (gradedOn_msg fun _ ↦ commit_le fuel hD) <|
    gapp (gradedOn_chals (sample_grade fuel) (Kap sh' κ')) <|
    gapp (gradedOn_msg (send_grade fuel)) <|
    gapp (gradedOn_msg (sendPlain_grade fuel (by norm_num))) <|
    gapp (gradedOn_msg fun _ ↦ grind_grade fuel) <|
    gapp (gradedOn_chal (positions_grade fuel _ _)) <|
    gapp (gradedOn_chal (sample_grade fuel)) <|
    gapp gradedOn_empty <|
    gapp (gradedOn_msg (sendPlain_grade fuel (by norm_num))) <|
    gapp gradedOn_empty hrest).mono (fun _ _ ↦ trivial) (by
      have hp := positions_counts (proverCounts fuel D) VerifierQueries.queryCounts rfl
        (Kap sh' κ' + sh.R) sh.t sh.t
      simp only [Verify.StepCounts.level, Verify.StepCounts.folds, Bool.false_eq_true,
        ite_false]
      rw [hp]
      simp only [proverCounts, Whir.Shape.ℓ]
      omega)

/-- The prover's queries on WHIR's levels: each level's at the commitment it makes, of the next
level's word. -/
def ladderQueries : {sh : Whir.Shape} → {κ : ℕ} → Ladder sh κ → ℕ
  | _, _, .last sh nf => (proverCounts fuel 0).level ⟨sh.ℓ, nf + 1, sh.R, sh.t, true⟩
  | _, _, @Ladder.cons sh sh' κ' L =>
    (proverCounts fuel (κ' + sh'.R)).level ⟨sh.ℓ, Kap sh' κ', sh.R, sh.t, false⟩ +
      ladderQueries L

theorem ladder_graded : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ),
    (ladderCodec (qops fuel) L).GradedOn queryGrade (fun _ ↦ True) (ladderQueries fuel L)
  | _, _, .last sh nf => finalCodec_graded fuel sh nf 0
  | _, _, @Ladder.cons sh sh' κ' L => levelCodec_graded fuel sh sh' κ' (ladder_graded L) le_rfl

/-! ## The compiled schedule's wire -/

theorem flockCodecOpt_graded (I : M3Instance) (o : Option (FlockRegion I.toShape)) (K : ℕ)
    (hK : ∀ r, o = some r → r.kBatch ≤ K) :
    (flockCodecOpt (qops fuel) I o).GradedOn queryGrade (fun _ ↦ True) (qc.flock K) := by
  rcases o with _ | r
  · exact gradedOn_empty.mono (fun _ _ ↦ trivial) (Nat.zero_le _)
  · refine (flockCodecOf_graded fuel r.kBatch).mono (fun _ _ ↦ trivial) ?_
    have := hK r rfl
    simp only [Verify.StepCounts.flock, Verify.StepCounts.rounds, Verify.StepCounts.round,
      VerifierQueries.queryCounts]
    nlinarith

/-- **The wire of the compiled schedule, counted**, on every transcript whose public-input
message has `nSent` values. -/
theorem compiledCodec_graded (I : M3Instance) (n : ℕ) {sh : Whir.Shape} {κ : ℕ}
    (L : Ladder sh κ) (K nSent : ℕ) (hK : ∀ r, I.flock = some r → r.kBatch ≤ K) :
    (compiledCodec (qops fuel) I n L).GradedOn queryGrade
      (fun tr ↦ (pubMessage tr).length = nSent)
      ((proverCounts fuel (κ + sh.R)).root + qc.bus I.μBus I.busClaims +
        qc.tables I.τmax I.tableColumns + qc.pub nSent + qc.flock K + 1 +
        (2 + ladderQueries fuel L)) := by
  exact GradedOn.mono ((((((((gradedOn_sendOne (G := fun _ ↦ True) fun _ ↦ commit_le fuel
      le_rfl).append
      (busCodec_graded fuel I)).append
      (tableCodec_graded fuel I)).append (pubCodec_graded fuel nSent)).append
      (flockCodecOpt_graded fuel I I.flock K hK)).append
      (gradedOn_chal (G := fun _ ↦ True) (sample_grade fuel))).append
      (gradedOn_empty (G := fun _ ↦ True))).append
      (gapp gradedOn_empty (gapp (gradedOn_msg (sendPlain_grade fuel (d := 2) (by norm_num)))
        (ladder_graded fuel L))))
    (fun tr h ↦ ⟨⟨⟨⟨⟨⟨⟨trivial, trivial⟩, trivial⟩, h⟩, trivial⟩, trivial⟩, trivial⟩, trivial⟩)
    (by simp only [proverCounts]; omega)

/-! ## The prover -/

theorem announce_grade (sz : Sizes) (ρ : ℕ) :
    queryGrade.P (StateT.lift (Writer.announce hashQuery sz ρ) : QM Unit) 8 :=
  queryGrade_lift fun ws ↦ by
    have := addScalars_queries (M := PrunedMerklePaths) (announcement sz ρ) ws
    simpa [Writer.announce, announcement] using this

theorem forIn_openings_grade : ∀ l : List ((Σ k, MerkleCommitment k) × List ℕ),
    queryGrade.P (forIn l PUnit.unit fun x _ ↦ match x with
        | (c, ps) => do
          StateT.lift (Writer.hintOpening (m := OracleComp hashSpec) (merkleOpen c.2 ps))
          return ForInStep.yield PUnit.unit) 0
  | [] => queryGrade.pure _
  | (c, ps) :: l => by
    rw [List.forIn_cons]
    refine queryGrade.of_eq (queryGrade.bind (k := 0) (queryGrade.of_eq (queryGrade.bind
      (queryGrade_lift (k := 0) fun _ ↦ itqb_pure _ _) fun _ ↦ queryGrade.pure _) rfl)
      fun r ↦ ?_) rfl
    rcases r with _ | _
    · exact queryGrade.pure _
    · exact forIn_openings_grade l

theorem hintOpenings_grade : queryGrade.P (hintOpenings : QM Unit) 0 := by
  unfold hintOpenings
  refine queryGrade.of_eq (queryGrade.bind (k := 0) queryGrade_get fun b ↦ ?_) rfl
  split
  · exact queryGrade.of_eq (queryGrade.bind (k := 0) queryGrade_failure fun _ ↦
      queryGrade.of_eq (queryGrade.bind (forIn_openings_grade _) fun _ ↦ queryGrade.pure _) rfl)
      rfl
  · exact queryGrade.of_eq (queryGrade.bind (forIn_openings_grade _) fun _ ↦
      queryGrade.pure _) rfl

/-- An accepted wire carries one public value per sent line. -/
private theorem pubLength_of_algebra' {prog : Program} {s : Sizes} {input : PublicInput}
    {shs : List Verify.LevelShape} {w : Verify.Wire} {rows : List (List (List K))}
    (h : Verify.algebra prog s input shs w rows = true) :
    w.pub.values.length =
      PublicInput.sentCount (Verify.leanVm prog s) ((Verify.leanVm prog s).publicLines input) := by
  unfold Verify.algebra at h
  rcases hb : Verify.leanVmBus prog s input w.bus with _ | b <;> simp only [hb] at h
  · cases h
  rcases ht : Verify.tableStep (Verify.leanVm prog s) b w.table with _ | t <;> simp only [ht] at h
  · cases h
  rcases hp : Verify.pubStep (Verify.leanVm prog s) t w.pub with _ | p <;> simp only [hp] at h
  · cases h
  simp only [Verify.leanVmBus, Option.bind_eq_bind, Option.bind_eq_some_iff] at hb
  obtain ⟨_, -, _, -, hb⟩ := hb
  cases hb
  simp only [Verify.tableStep, Option.bind_eq_bind, Option.bind_eq_some_iff] at ht
  obtain ⟨_, -, _, -, _, -, ht⟩ := ht
  split_ifs at ht
  cases ht
  simp only [Verify.pubStep] at hp
  split_ifs at hp with hacc
  simp only [PublicInput.accepts, Bool.and_eq_true, decide_eq_true_eq] at hacc
  exact hacc.1

theorem nonempty_of_sampleable (α : Type) [SampleableType α] : Nonempty α :=
  (support_nonempty ($ᵗ α)).elim fun x _ ↦ ⟨x⟩

theorem flock_kBatch (prog : Program) (s : Sizes) :
    ∀ r, (Verify.leanVm prog s).flock = some r → r.kBatch ≤ s.τ 5 := fun r h ↦ by
  cases h
  exact le_rfl

/-- The queries of the compiled schedule's wire at the deployed instance. -/
def wireQueries (fuel : ℕ) (prog : Program) (s : Sizes) (input : PublicInput) {sh : Whir.Shape}
    {κ : ℕ} (L : Ladder sh κ) : ℕ :=
  (proverCounts fuel (κ + sh.R)).root +
    qc.bus (Verify.leanVm prog s).μBus (Verify.leanVm prog s).busClaims +
    qc.tables (Verify.leanVm prog s).τmax (Verify.leanVm prog s).tableColumns +
    qc.pub (PublicInput.sentCount (Verify.leanVm prog s)
      ((Verify.leanVm prog s).publicLines input)) + qc.flock (s.τ 5) + 1 +
    (2 + ladderQueries fuel L)

theorem writeProof_grade {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {s : Sizes} (hsat : SatisfiedBy prog input w)
    (hws : Sizes.ofWitness w = some s) (hs : s.Admissible prog) {ρ : ℕ} (hρ : validRate ρ) :
    queryGrade.P (writeProof hashQuery (qops fuel) Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ
      input (stackOf Blake2sFlock.blake2sFlockSpec prog s w))
      (8 + (wireQueries fuel prog s input (leanIsaChain prog s hs ρ hρ).ladder + 0)) := by
  unfold writeProof
  refine queryGrade.bind (announce_grade s ρ) fun _ ↦
    queryGrade.bind ?_ fun _ ↦ hintOpenings_grade
  have := fun i ↦ nonempty_of_sampleable
    ((listBindingSpec (Verify.leanVm prog s) (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder).Challenge i)
  refine Prover.runWith_graded _ _ _ (𝓖 := queryGrade) (fun f x k h ↦ queryGrade_of_map f x k h)
    (fun x k k' h hk ↦ queryGrade_mono h hk)
    (compiledCodec_graded fuel (Verify.leanVm prog s) (Verify.nLanes prog s)
      (leanIsaChain prog s hs ρ hρ).ladder (s.τ 5) _ (flock_kBatch prog s)) fun ch ↦ ?_
  have hr := Prover.runWithChallenges_eq_of_run_eq _ (compiledProver_run (Verify.leanVm prog s)
    (leanIsa_conditions Blake2sFlock.blake2sFlockSpec prog s)
    (leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ)
    (leanIsaChain prog s hs ρ hρ).ladder
    ((leanIsaChain prog s hs ρ hρ).ladder.headPar (leanIsaChain prog s hs ρ hρ).pars).hb
    (input, fun i ↦ i.elim0) (stackOf Blake2sFlock.blake2sFlockSpec prog s w)) ch
  obtain ⟨so, hacc, -, -⟩ := Prover.accepts_of_perfectCompleteness (pure ()) (fun t ↦ isEmptyElim t)
    (R := (compiledDef prog s hs ρ hρ).red.toReduction)
    (listBinding_deployed_perfectCompleteness Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ
      (pure ()) (fun t ↦ isEmptyElim t)) (stmt := (input, fun i ↦ i.elim0))
    (m3Holds_stackOf hsat hws) ch
  have halg := Compile.phasesAgree prog s hs ρ hρ input _ so hacc
  have h₁ := pubLength_of_algebra' halg
  simp only [DecodeChain.wireOf, DecodeChain.pubWireOf] at h₁
  rw [hr]
  exact h₁

/-- **The honest prover's queries**, at a witness of the constraint statement with admissible
sizes and a valid rate: the seed's three, the announcement's eight, and the wire's. -/
theorem isTotalQueryBound_proveWith {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {s : Sizes} (hsat : SatisfiedBy prog input w)
    (hws : Sizes.ofWitness w = some s) (hs : s.Admissible prog) {ρ : ℕ} (hρ : validRate ρ) :
    IsTotalQueryBound (proveWith hashQuery fuel Blake2sFlock.blake2sFlockSpec prog input w ρ)
      (3 + (8 + wireQueries fuel prog s input (leanIsaChain prog s hs ρ hρ).ladder)) := by
  unfold proveWith proveFrom
  rw [hws]
  dsimp only
  rw [dite_eq_left ⟨hs, hρ⟩]
  unfold runProofFrom
  refine isTotalQueryBound_bind (VerifierQueries.isTotalQueryBound_seedWith prog input)
    fun fs ↦ isTotalQueryBound_bind (n₂ := 0) ?_ fun _ ↦ itqb_pure _ _
  have hw := writeProof_grade fuel hsat hws hs hρ ⟨#[], #[]⟩ ⟨fs, #[], #[]⟩
  have : runWrite ((writeProof hashQuery (qops fuel) Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ
      input (stackOf Blake2sFlock.blake2sFlockSpec prog s w)).run' ⟨#[], #[]⟩) fs =
      (Option.map fun p ↦ (p.1.1, p.2)) <$> runQ (writeProof hashQuery (qops fuel)
        Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ input
        (stackOf Blake2sFlock.blake2sFlockSpec prog s w)) ⟨#[], #[]⟩ ⟨fs, #[], #[]⟩ := by
    simp only [runWrite, runQ, StateT.run'_eq, StateT.run_map, OptionT.run_map]
  rw [this]
  exact (isQueryBound_map_iff _ _ _ _ _).mpr (hw.mono (le_of_eq (by simp)))

/-! ## In closed form -/

/-- The prover's counts with the grinds left out. -/
def proverCounts0 (D : ℕ) : Verify.StepCounts := ⟨1, 1, 2 ^ (D + 1) + 2, fun _ ↦ 0⟩

/-- WHIR's levels by their shapes, the grinds left out: a level before the last commits to the
next level's word, of `msgLog - fold' + rate'` positions' bits. -/
def shapeQueries0 : List Verify.LevelShape → ℕ
  | [] => 0
  | [sh] => (proverCounts0 0).level sh
  | sh :: sh₂ :: rest =>
    (proverCounts0 (sh.msgLog - sh₂.fold + sh₂.rate)).level sh + shapeQueries0 (sh₂ :: rest)

theorem tail_counts (c c' : Verify.StepCounts) (h₁ : c.sample = c'.sample)
    (h₂ : c.scalar = c'.scalar) : ∀ k, c.tail k = c'.tail k
  | 0 => rfl
  | k + 1 => by simp only [Verify.StepCounts.tail, h₁, h₂, tail_counts c c' h₁ h₂ k]

theorem level_split (D : ℕ) (sh : Verify.LevelShape) :
    (proverCounts fuel D).level sh = (proverCounts0 D).level sh + (fuel + 2) := by
  have hp := positions_counts (proverCounts fuel D) (proverCounts0 D) rfl (sh.msgLog + sh.rate)
    sh.queries sh.queries
  have ht := tail_counts (proverCounts fuel D) (proverCounts0 D) rfl rfl sh.msgLog
  simp only [Verify.StepCounts.level, hp, ht]
  simp only [proverCounts, proverCounts0, Verify.StepCounts.folds]
  split <;> omega

theorem shapes_head : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ),
    ∃ x rest, L.shapes = x :: rest ∧ x.fold = sh.ℓ ∧ x.rate = sh.R
  | _, _, .last _ _ => ⟨_, _, rfl, rfl, rfl⟩
  | _, _, .cons _ _ => ⟨_, _, rfl, rfl, rfl⟩

theorem ladderQueries_eq : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ),
    ladderQueries fuel L = shapeQueries0 L.shapes + L.shapes.length * (fuel + 2)
  | _, _, .last sh nf => by
    simp only [ladderQueries, Ladder.shapes, shapeQueries0, level_split, List.length_singleton]
    omega
  | _, _, @Ladder.cons sh sh' κ' L => by
    obtain ⟨x, rest, hL, hf, hr⟩ := shapes_head L
    have ih := ladderQueries_eq L
    simp only [ladderQueries, Ladder.shapes, hL, shapeQueries0, level_split, List.length_cons]
      at ih ⊢
    rw [ih, hf, hr]
    have : Kap sh' κ' - sh'.ℓ + sh'.R = κ' + sh'.R := by simp only [Kap]; omega
    rw [this]
    ring

/-- WHIR's levels over the window of its parameters: the levels' counts without the grinds, the
number of levels, and the level-0 commitment's positions' bits. One decision on the window. -/
theorem window_key : ∀ μ < Parameters.Whir.maxLogStack + 1,
    ∀ r < Parameters.Whir.maxLogInvRate + 1, ∀ ls ∈ Parameters.Whir.ladder μ r,
      shapeQueries0 (Verify.levelShapes μ ls) ≤ 130023647 ∧
        (Verify.levelShapes μ ls).length ≤ 6 ∧
        ∀ x ∈ (Verify.levelShapes μ ls).head?, μ - x.fold + x.rate ≤ 26 := by
  decide +kernel

/-- **The wire's queries in closed form**, at admissible sizes and a valid rate. -/
theorem wireQueries_le {prog : Program} {input : PublicInput} {s : Sizes}
    (hs : s.Admissible prog) {ρ : ℕ} (hρ : validRate ρ) :
    wireQueries fuel prog s input (leanIsaChain prog s hs ρ hρ).ladder ≤
      (2 ^ 27 + 2) + qc.bus 55 192 + qc.tables 40 110 + qc.pub 2 + qc.flock maxLogRows + 1 +
        (2 + (130023647 + 6 * (fuel + 2))) := by
  obtain ⟨levels, hl, hsh, -, -⟩ := leanIsaChain_walk hs hρ
  have hadm := admissible_of_sizes hs hρ
  obtain ⟨hW, hlen, hd⟩ := window_key _ (Nat.lt_succ_of_le hadm.2.1) ρ
    (Nat.lt_succ_of_le hadm.2.2.2) levels hl
  rw [hsh] at hW hlen hd
  have hm : s.logMem ≤ maxLogMem := hs.2.1
  have hτ : ∀ j, s.τ j ≤ maxLogRows := hs.2.2.1
  -- the level-0 commitment
  obtain ⟨x, rest, hL, hf, hr⟩ := shapes_head (leanIsaChain prog s hs ρ hρ).ladder
  have hd0 := hd x (by rw [hL]; rfl)
  have hh := leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ
  have hroot : (proverCounts fuel ((leanIsaChain prog s hs ρ hρ).κ +
      (leanIsaChain prog s hs ρ hρ).sh.R)).root ≤ 2 ^ 27 + 2 := by
    simp only [proverCounts]
    have : (leanIsaChain prog s hs ρ hρ).κ + (leanIsaChain prog s hs ρ hρ).sh.R ≤ 26 := by
      rw [hf, hr] at hd0
      change _ = leanIsaμ prog s at hh
      omega
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.succ_le_succ this)
    omega
  -- the phases
  have hbus : qc.bus (Verify.leanVm prog s).μBus (Verify.leanVm prog s).busClaims ≤
      qc.bus 55 192 := by
    have hμ : (Verify.leanVm prog s).μBus ≤ 55 :=
      leanIsa_μBus_le_of Blake2sFlock.blake2sFlockSpec (prog := prog) hm hτ
    have hc := busClaims_le (Verify.leanVm prog s)
    rw [show (Verify.leanVm prog s).boundary.length = 6 from rfl] at hc
    have key : ∀ m < 56, qc.layers (Verify.gkrRadices m) 0 ≤
        qc.layers (Verify.gkrRadices 55) 0 := by decide +kernel
    have := key _ (Nat.lt_succ_of_le hμ)
    simp only [Verify.StepCounts.bus, VerifierQueries.queryCounts] at this ⊢
    omega
  have htab : qc.tables (Verify.leanVm prog s).τmax (Verify.leanVm prog s).tableColumns ≤
      qc.tables 40 110 := by
    have hτmax : (Verify.leanVm prog s).τmax ≤ 40 :=
      Finset.sup_le fun j _ ↦ leanIsa_height_le_of hm hτ j.1
    have hw : ∑ j, (Verify.leanVm prog s).width j = 110 := by
      show ∑ j : Fin 9, LeanIsa.width j = 110
      decide +kernel
    have hc : (Verify.leanVm prog s).tableColumns ≤ 110 :=
      (sum_sumcheckTables_le (Verify.leanVm prog s) (Verify.leanVm prog s).width).trans hw.le
    simp only [Verify.StepCounts.tables, Verify.StepCounts.rounds, Verify.StepCounts.round,
      VerifierQueries.queryCounts]
    omega
  have hfl : qc.flock (s.τ 5) ≤ qc.flock maxLogRows := by
    have := hτ 5
    simp only [Verify.StepCounts.flock, Verify.StepCounts.rounds, Verify.StepCounts.round,
      VerifierQueries.queryCounts]
    omega
  have hpub : PublicInput.sentCount (Verify.leanVm prog s)
      ((Verify.leanVm prog s).publicLines input) = 2 := rfl
  have hlad := ladderQueries_eq fuel (leanIsaChain prog s hs ρ hρ).ladder
  have hmul : (leanIsaChain prog s hs ρ hρ).ladder.shapes.length * (fuel + 2) ≤
      6 * (fuel + 2) := Nat.mul_le_mul_right _ hlen
  unfold wireQueries
  rw [hpub, hlad]
  omega

/-- **The honest prover's queries in closed form**, at a witness of the constraint statement whose
sizes keep the stack within `2^maxMu`, at a valid rate: at most `264246250 + 6 · fuel`. -/
theorem isTotalQueryBound_proveWith_closed {prog : Program} {input : PublicInput} {κ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} {s : Sizes} (hsat : SatisfiedBy prog input w)
    (hws : Sizes.ofWitness w = some s) (hμ : leanIsaμ prog s ≤ maxMu) {ρ : ℕ}
    (hρ : validRate ρ) :
    IsTotalQueryBound (proveWith hashQuery fuel Blake2sFlock.blake2sFlockSpec prog input w ρ)
      (264246250 + 6 * fuel) := by
  have hs := (admissible_iff_of_satisfiedBy hsat hws).mpr hμ
  refine (isTotalQueryBound_proveWith fuel hsat hws hs hρ).mono ?_
  have := wireQueries_le fuel (input := input) hs hρ
  have e : (2 ^ 27 + 2) + qc.bus 55 192 + qc.tables 40 110 + qc.pub 2 + qc.flock maxLogRows + 1 +
      2 + 130023647 = 264246227 := by decide +kernel
  omega

end Ops

end Prove

end
end LeanerVM.Protocol
