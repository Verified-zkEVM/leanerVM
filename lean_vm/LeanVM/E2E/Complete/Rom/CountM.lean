/-
  LeanVM.E2E.Complete.Rom.CountM

  T6-prob: the hash queries of the honest prover's monadic pieces at the random oracle: the
  Fiat–Shamir run and the fresh claims' run, the seed and a statement's digest, the batching's
  honest hints, and the node's checks with their log (hash calls, not block prefixes).
-/

module

public import LeanVM.E2E.Complete.Rom.MonadicM
public import LeanVM.E2E.Reduction.SphincsBound
public import LeanVM.Protocol.Verifier.Cost

/-!
# The pieces' queries

`docs/roadmap/t6-prob.md` §4.4. Each piece of `MonadicM.lean` at the hash a query (`queryH`)
makes a bounded number of queries (`IsTotalQueryBound`), as a function of its inputs:

* the Fiat–Shamir run of a program of cost `n` at height `h` at most `n · proverFactor h fuel`
  (`isTotalQueryBound_fsRunM`, as the honest prover's `isTotalQueryBound_proveFromM`); the fresh
  claims' run at most `leanVmCost · proverFactor costHeight fuel` (`claimsProg`, a prefix of V°,
  costs at most `leanVmCost`: `costLE_claimsProg`);
* the IV `2`, a statement's digest `5` (`7` with the IV);
* the batching's honest hints `honestBatchQueries` (`isTotalQueryBound_honestBatchM`);
* the node's checks and their logged run `nodeChecksQueries s w`
  (`isTotalQueryBound_nodeLogPairsWithM`): the statement's digest `5`; per child its digest `5`,
  the deferring verifier's seed `1` and program `leanVmCost` (`costLE_deferredProgram`, the
  deferred claims' evaluations hashing nothing); per direct leanXMSS signature
  `xmssVerifyBound`, per direct leanSPHINCS signature `sphincsVerifyBound`; per direct DA
  opening `daQueries` of its rows (`isTotalQueryBound_commitCodewordsWith`, the trees' levels
  halving); the children's claims `5` each; the batching `batchQueries`.

Under the deployed limits, DA openings of at most `LeanDa.maxRows` rows, shaped children and
the honest hints' round counts, the node's checks make at most `nodeChecksBound` queries
(`nodeChecksQueries_le`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Guest.Batch LeanVM.Guest.B1.Main LeanVM.E2E LeanVM.Protocol.Compile.Rom
open OracleComp OracleSpec

@[expose] public section

/-! ## Generic facts -/

/-- One query. -/
theorem isTotalQueryBound_queryH_one (x : Bytes) : IsTotalQueryBound (queryH x) 1 := by
  have h := isTotalQueryBound_queryH_bind (f := pure) (n := 0) x fun _ ↦ trivial
  rwa [bind_pure] at h

/-- A map makes the queries of its computation. -/
theorem isTotalQueryBound_map_of {α β : Type} {oa : OracleComp HashSpec α} {n : ℕ} (f : α → β)
    (h : IsTotalQueryBound oa n) : IsTotalQueryBound (f <$> oa) n :=
  (isQueryBound_map_iff oa f n _ _).mpr h

/-- Every value of a `mapM` has the list's length. -/
theorem length_of_mem_support_mapM {α β : Type} (f : α → OracleComp HashSpec β) :
    ∀ (l : List α) (x : List β), x ∈ support (l.mapM f) → x.length = l.length
  | [], x, hx => by simp at hx; simp [hx]
  | a :: l, x, hx => by
    simp only [List.mapM_cons, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
    obtain ⟨b, -, bs, hbs, rfl⟩ := hx
    simp [length_of_mem_support_mapM f l bs hbs]

/-! ## The Fiat–Shamir run -/

section FsRun

/-- **The Fiat–Shamir run's queries**: from a history whose commitments have height at most
`height`, a program of cost `n` makes at most `n · proverFactor height fuel` queries. -/
theorem isTotalQueryBound_fsRunM (S : Strategy) (fuel height : ℕ) {α : Type} :
    ∀ (p : Prog α) (cv : Digest) (h : List Ev) (n : ℕ) (Q : α → Prop), p.Costs height n Q →
      (∀ c ∈ commits h, c.1 ≤ height) →
      IsTotalQueryBound (fsRunM queryH S fuel p cv h) (n * proverFactor height fuel)
  | .ret _, _, _, _, _, _, _ => trivial
  | .fail, _, _, _, _, _, _ => trivial
  | .read k, cv, h, n, Q, hp, hs => by
    simp only [fsRunM]
    refine (isTotalQueryBound_queryH_bind (n := (n - 1) * proverFactor height fuel) _
      fun cv' ↦ isTotalQueryBound_fsRunM S fuel height _ cv' (h ++ [Ev.read (S.msg h)]) (n - 1) Q
        (hp.2 _) (by simpa [commits_append, commits] using hs)).mono ?_
    have h1 := hp.1
    have hF := one_le_proverFactor height fuel
    generalize proverFactor height fuel = F at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul, one_mul]
    omega
  | .sample k, cv, h, n, Q, hp, hs => by
    simp only [fsRunM]
    refine (isTotalQueryBound_queryH_bind (n := (n - 1) * proverFactor height fuel) _
      fun cv' ↦ isTotalQueryBound_fsRunM S fuel height _ cv'
        (h ++ [Ev.sample (challengeOf cv')]) (n - 1) Q (hp.2 _)
          (by simpa [commits_append, commits] using hs)).mono ?_
    have h1 := hp.1
    have hF := one_le_proverFactor height fuel
    generalize proverFactor height fuel = F at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul, one_mul]
    omega
  | .grind bits k, cv, h, n, Q, hp, hs => by
    simp only [fsRunM]
    have hs' : ∀ c ∈ commits (h ++ [Ev.grind bits]), c.1 ≤ height := by
      simpa [commits_append, commits] using hs
    refine (isTotalQueryBound_bind (isTotalQueryBound_findNonceM bits cv fuel)
      (n₂ := (n - 3) * proverFactor height fuel + 1) fun o ↦ ?_).mono ?_
    · split
      · trivial
      · exact isTotalQueryBound_queryH_bind _ fun cv' ↦
          isTotalQueryBound_fsRunM S fuel height k cv' (h ++ [Ev.grind bits]) (n - 3) Q hp.2 hs'
    · have h1 := hp.1
      have hF := fuel_lt_proverFactor height fuel
      generalize proverFactor height fuel = F at *
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_mul]
      omega
  | .commit ht w k, cv, h, n, Q, hp, hs => by
    simp only [fsRunM]
    split
    · have hs' : ∀ c ∈ commits (h ++ [Ev.commit ht w (S.word h)]), c.1 ≤ height := by
        simp only [commits_append, commits, List.mem_append, List.mem_singleton]
        rintro c (hc | rfl)
        · exact hs c hc
        · exact hp.1
      refine (isTotalQueryBound_bind (isTotalQueryBound_treeRootM ht (S.word h))
        (n₂ := (n - 2) * proverFactor height fuel + 1 + 1) fun root ↦
          isTotalQueryBound_queryH_bind (n := (n - 2) * proverFactor height fuel + 1) _
            fun cv0 ↦ isTotalQueryBound_queryH_bind (n := (n - 2) * proverFactor height fuel) _
              fun cv1 ↦ isTotalQueryBound_fsRunM S fuel height k cv1
                (h ++ [Ev.commit ht w (S.word h)]) (n - 2) Q hp.2.2 hs').mono ?_
      have h1 := hp.2.1
      have h2 : 2 ^ (ht + 1) ≤ 2 ^ (height + 1) := Nat.pow_le_pow_right (by norm_num) (by
        have := hp.1; omega)
      have hF := pow_lt_proverFactor height fuel
      generalize proverFactor height fuel = F at *
      generalize 2 ^ (height + 1) = A at *
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_mul]
      omega
    · trivial
  | .query i ps k, cv, h, n, Q, hp, hs => by
    simp only [fsRunM]
    split
    · trivial
    · rename_i ht w word hc
      have hs' : ∀ c ∈ commits (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))]),
          c.1 ≤ height := by
        simpa [commits_append, commits] using hs
      exact (isTotalQueryBound_fsRunM S fuel height _ cv _ _ Q (hp.2 _) hs').mono
        (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

/-- The Fiat–Shamir run of a program of cost `n` at `height`, from the start. -/
theorem isTotalQueryBound_fsRunM_nil {α : Type} {P : Prog α} {height n : ℕ}
    (hP : P.CostLE height n) (S : Strategy) (seed : Digest) (fuel : ℕ) :
    IsTotalQueryBound (fsRunM queryH S fuel P seed []) (n * proverFactor height fuel) :=
  isTotalQueryBound_fsRunM S fuel height P seed [] n _ hP (by simp [commits])

end FsRun

/-! ## The costs of V°'s prefix and of the deferring verifier -/

section Costs

variable {height : ℕ}

/-- An entry of a list of bounded numbers is bounded. -/
theorem getD_le_of_forall_le {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) (i : ℕ) :
    l.getD i 0 ≤ M := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some x => exact h x (List.mem_of_getElem? hi)

/-- The bus phase's reads before the bytecode's value. -/
theorem costs_busPre (layout : Verifier.Layout) :
    Prog.Costs height (busPre layout)
      (busBits + 1 + (2 + gkrCost (busLayout [0, layout.logMemory, layout.logBytecode]
        layout.push).depth 0) + 5) fun _ ↦ True := by
  refine Prog.Costs.seq (Prog.Costs.sampleN _) (fun _ _ ↦ Prog.Costs.seq Prog.Costs.sampleE
    (fun _ _ ↦ Prog.Costs.seq (costs_verifyGkrGrandProducts _) (fun r _ ↦ ?_) ?_) ?_) ?_
  · refine Prog.Costs.seq (Prog.Costs.require (n := 0) _) (fun _ _ ↦ Prog.Costs.seq
      (Prog.Costs.readN 3)
      (fun _ _ ↦ Prog.Costs.seq Prog.Costs.readE (fun _ _ ↦ Prog.Costs.seq Prog.Costs.readE
        (fun _ _ ↦ trivial) ?_) ?_) ?_) ?_ <;> omega
  all_goals omega

/-- The bus phase's reads, on a built layout. -/
theorem costs_busPre_le {layout : Verifier.Layout} (h : LayoutBounds layout) :
    Prog.Costs height (busPre layout) (busBits + 1 + (2 + gkrBound) + 5) fun _ ↦ True :=
  (costs_busPre layout).mono (by have := gkrCost_le _ (pushDepth_le h); omega) fun _ h ↦ h

/-- The lincheck's reads before the matrices' value. -/
theorem costs_linPre (zc : ZerocheckResult) :
    Prog.Costs height (linPre zc) 89 fun _ ↦ True := by
  refine Prog.Costs.seq Prog.Costs.sampleE (fun _ _ ↦ Prog.Costs.seq (costs_sumcheck _ _ _)
    (fun r _ ↦ ?_) ?_) ?_
  · exact Prog.Costs.seq (Prog.Costs.readN kBits) (fun _ _ ↦ trivial)
      (by simp only [List.length_replicate, flockNumLincheckRounds_eq, kBits,
        show max 3 2 = 3 from rfl]; omega)
  all_goals (try simp only [List.length_replicate, flockNumLincheckRounds_eq,
    show max 3 2 = 3 from rfl])
  all_goals omega

/-- **The cost of V°'s prefix** reading the fixed claims: at most `leanVmCost`. -/
theorem costLE_claimsProg (bc : List K) (pd : Digest) :
    (claimsProg bc pd).CostLE costHeight leanVmCost := by
  unfold claimsProg
  refine (Prog.Costs.bind (m := leanVmCost - 8) (costs_readSizes bc) fun a hp ↦ ?_).mono
    (by unfold leanVmCost; omega) fun _ h ↦ h
  obtain ⟨hl, -, -, -, -⟩ := hp
  have hblake : a.1.tableLogHeights.getD opBlake2s 0 ≤ 32 :=
    getD_le_of_forall_le hl.heights_le opBlake2s
  refine (Prog.Costs.bind (costs_commitStack _ _ fun levels h ↦ (ladder_cost _ _ levels h).2.1)
    fun _ _ ↦ Prog.Costs.bind (costs_busPre_le hl) fun t _ ↦
      Prog.Costs.bind (m := _) (n := 0) (Prog.Costs.pure0 _) fun v _ ↦
        Prog.Costs.bind (costs_tablePhase hl _) fun _ _ ↦
          Prog.Costs.bind (costs_publicInputPhase _ _) fun _ _ ↦
            Prog.Costs.bind (costs_verifyFlockZerocheck _) fun zc _ ↦
              Prog.Costs.bind (costs_linPre zc) fun u _ ↦
                (show Prog.Costs costHeight (Prog.ret (freshOf a.1 t zc u)) 0 fun _ ↦ True
                  from trivial)).mono ?_ fun _ h ↦ h
  unfold leanVmCost
  simp only [flockBound, blake2sR1csLogSize] at *
  omega

/-- The claimed bytecode value reads nothing. -/
theorem costs_claimed_bytecode (c : FixedClaims) (words : List K) (point : List E) :
    Prog.Costs height ((Evaluations.claimed c).bytecode words point) 0 fun _ ↦ True :=
  Prog.Costs.seq (Prog.Costs.require (n := 0) _) (fun _ _ ↦ trivial) le_rfl

/-- The claimed matrices' value reads nothing. -/
theorem costs_claimed_matrices (c : FixedClaims) (alpha zSkip : E) (chiIn chiInPrime s : List E) :
    Prog.Costs height ((Evaluations.claimed c).matrices alpha zSkip chiIn chiInPrime s) 0
      fun _ ↦ True :=
  Prog.Costs.seq (Prog.Costs.require (n := 0) _) (fun _ _ ↦ trivial) le_rfl

/-- The bus phase with claimed values, on a built layout. -/
theorem costs_verifyBusBalance_claimed (c : FixedClaims) {layout : Verifier.Layout}
    (h : LayoutBounds layout) :
    Prog.Costs height (verifyBusBalance (.claimed c) layout) (busBits + 1 + (2 + gkrBound) + 5)
      fun _ ↦ True := by
  rw [verifyBusBalance_eq]
  refine (Prog.Costs.bind (costs_busPre_le h) fun t _ ↦ Prog.Costs.bind (m := 0)
    (costs_claimed_bytecode c _ _) fun v _ ↦
      (show Prog.Costs height (Prog.ret _) 0 fun _ ↦ True from trivial)).mono (by omega)
        fun _ h ↦ h

/-- Flock with claimed values. -/
theorem costs_verifyFlock_claimed (c : FixedClaims) (logN : ℕ) :
    Prog.Costs height (verifyFlock (.claimed c) logN) (4 * (logN - 13) + 177) fun _ ↦ True := by
  unfold verifyFlock
  refine Prog.Costs.seq (costs_verifyFlockZerocheck logN) (fun zc _ ↦ ?_) (by omega)
  rw [verifyFlockLincheck_eq]
  refine (Prog.Costs.bind (costs_linPre zc) fun u _ ↦ Prog.Costs.bind (m := 0)
    (costs_claimed_matrices c _ _ _ _ _) fun mv _ ↦ Prog.Costs.bind (m := 0)
      (Prog.Costs.require (n := 0) _) fun _ _ ↦
        (show Prog.Costs height (Prog.ret _) 0 fun _ ↦ True from trivial)).mono (by omega)
          fun _ h ↦ h

/-- **The cost of `verify_execution` with claimed values**: the deployed bound. -/
theorem costs_verifyExecution_claimed (c : FixedClaims) (bytecode : List K)
    (publicInput : Digest) :
    Prog.Costs costHeight (verifyExecution (.claimed c) bytecode publicInput) leanVmCost
      fun _ ↦ True := by
  unfold leanVmCost
  refine Prog.Costs.seq (costs_readSizes bytecode) (fun p hp ↦ ?_) (by omega)
  obtain ⟨layout, logInverseRate⟩ := p
  obtain ⟨hl, -, -, -, -⟩ := hp
  have hblake : layout.tableLogHeights.getD opBlake2s 0 ≤ 32 :=
    getD_le_of_forall_le hl.heights_le opBlake2s
  refine Prog.Costs.seq (costs_commitStack _ _ fun levels h ↦ (ladder_cost _ _ levels h).2.1)
    (fun _ _ ↦ Prog.Costs.seq (costs_verifyBusBalance_claimed c hl) (fun bus _ ↦ Prog.Costs.seq
      (costs_tablePhase hl bus) (fun claims _ ↦ Prog.Costs.seq
        (costs_publicInputPhase layout publicInput) (fun publicClaims _ ↦ Prog.Costs.seq
          (costs_verifyFlock_claimed c _) (fun r _ ↦ ?_) ?_) ?_) ?_) ?_) ?_
  · obtain ⟨flockPoint, flockS⟩ := r
    refine Prog.Costs.seq (costs_ringSwitch flockPoint flockS) (fun r _ ↦ ?_) ?_
    · obtain ⟨ringTarget, ringWeight⟩ := r
      refine (costs_verifyStackedOpening _ _ _ whirBound fun levels h ↦
        ⟨(ladder_cost _ _ levels h).1, (ladder_cost _ _ levels h).2.2⟩).mono ?_
          fun _ h ↦ h
      simp only [flockBound, blake2sR1csLogSize] at *
      omega
    · simp only [flockBound, blake2sR1csLogSize] at *
      omega
  all_goals simp only [flockBound, blake2sR1csLogSize] at *
  all_goals omega

/-- **The cost of the deferring verifier's program**: at most `leanVmCost`. -/
theorem costLE_deferredProgram (c : FixedClaims) (bytecode : List K) (publicInput : Digest) :
    (deferredProgram c bytecode publicInput).CostLE costHeight leanVmCost :=
  Prog.Costs.seq (costs_verifyExecution_claimed c bytecode publicInput) (fun _ _ ↦ trivial) le_rfl

end Costs

/-- **The fresh claims' run's queries.** -/
theorem isTotalQueryBound_freshRunM (S : Strategy) (fuel : ℕ) (bc : List K) (pd seed : Digest) :
    IsTotalQueryBound (freshRunM queryH S fuel bc pd seed)
      (leanVmCost * proverFactor costHeight fuel) :=
  isTotalQueryBound_map_of _ (isTotalQueryBound_fsRunM_nil (costLE_claimsProg bc pd) S seed fuel)

/-! ## The seed and the statement's digest -/

/-- The IV makes two queries. -/
theorem isTotalQueryBound_seedOfM : IsTotalQueryBound (seedOfM queryH) 2 :=
  isTotalQueryBound_queryH_bind _ fun _ ↦ isTotalQueryBound_queryH_one _

/-- A statement's digest makes five queries. -/
theorem isTotalQueryBound_statementDigestWith (seed : Digest) (s : NodeStatement) :
    IsTotalQueryBound (statementDigestWith queryH seed s) 5 :=
  isTotalQueryBound_bind (n₁ := 3) (n₂ := 2)
    (isTotalQueryBound_bind (n₁ := 1) (n₂ := 2) (isTotalQueryBound_queryH_one _) fun _ ↦
      isTotalQueryBound_bind (n₁ := 1) (n₂ := 1) (isTotalQueryBound_queryH_one _) fun _ ↦
        isTotalQueryBound_queryH_one _) fun _ ↦
    isTotalQueryBound_bind (n₁ := 1) (n₂ := 1) (isTotalQueryBound_queryH_one _) fun _ ↦
      isTotalQueryBound_queryH_one _

/-- A node's statement digest, from the IV, makes seven queries. -/
theorem isTotalQueryBound_digestOfM (s : NodeStatement) :
    IsTotalQueryBound (digestOfM queryH s) 7 :=
  isTotalQueryBound_bind (n₁ := 2) (n₂ := 5) isTotalQueryBound_seedOfM fun _ ↦
    isTotalQueryBound_statementDigestWith _ s

/-! ## Computations over a chain state -/

section Chain

/-- **A chain computation's queries**: at most `n` from every chain state. -/
def CostS {σ α : Type} (x : StateT σ (OracleComp HashSpec) α) (n : ℕ) : Prop :=
  ∀ s, IsTotalQueryBound (x.run s) n

theorem CostS.mono {σ α : Type} {x : StateT σ (OracleComp HashSpec) α} {n n' : ℕ}
    (h : CostS x n) (hn : n ≤ n') : CostS x n' := fun s ↦ (h s).mono hn

theorem costS_pure {σ α : Type} (a : α) : CostS (pure a : StateT σ (OracleComp HashSpec) α) 0 :=
  fun _ ↦ trivial

theorem costS_bind {σ α β : Type} {x : StateT σ (OracleComp HashSpec) α}
    {f : α → StateT σ (OracleComp HashSpec) β} {a b : ℕ} (hx : CostS x a)
    (hf : ∀ v, CostS (f v) b) : CostS (x >>= f) (a + b) := fun s ↦ by
  rw [StateT.run_bind]
  exact isTotalQueryBound_bind (hx s) fun p ↦ hf p.1 p.2

theorem costS_observe (x : E) : CostS (observeWith queryH x) 1 := fun s ↦ by
  simp only [observeWith, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
    monadLift_self, StateT.run_set, bind_pure_comp]
  exact isTotalQueryBound_map_of _ (isTotalQueryBound_queryH_one _)

theorem costS_squeeze : CostS (squeezeWith queryH) 1 := fun s ↦ by
  simp only [squeezeWith, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_monadLift,
    monadLift_self, StateT.run_set, bind_pure_comp, StateT.run_map]
  exact isTotalQueryBound_bind (n₂ := 0)
    (isTotalQueryBound_map_of _ (isTotalQueryBound_queryH_one _))
    fun _ ↦ trivial

/-- A batching sumcheck makes three queries per round. -/
theorem costS_batchRoundsWith : ∀ (claim : E) (rounds : List (E × E)),
    CostS (batchRoundsWith queryH claim rounds) (3 * rounds.length)
  | _, [] => costS_pure _
  | claim, (g1, gInf) :: rest => by
    simp only [batchRoundsWith]
    refine (costS_bind (costS_observe _) fun _ ↦ costS_bind (costS_observe _) fun _ ↦
      costS_bind costS_squeeze fun r ↦ costS_bind (costS_batchRoundsWith _ rest) fun p ↦
        costS_pure _).mono ?_
    simp only [List.length_cons]
    omega

/-- A loop over a list: the sum of its bodies' bounds. -/
theorem costS_forIn {σ α β : Type} (f : α → β → StateT σ (OracleComp HashSpec) (ForInStep β))
    (g : α → ℕ) (hf : ∀ a b, CostS (f a b) (g a)) :
    ∀ (l : List α) (init : β), CostS (forIn l init f) (l.map g).sum
  | [], _ => costS_pure _
  | a :: l, init => by
    rw [List.forIn_cons, List.map_cons, List.sum_cons]
    refine costS_bind (hf a init) fun r ↦ ?_
    cases r with
    | done b => exact (costS_pure b).mono (Nat.zero_le _)
    | yield b => exact costS_forIn f g hf l b

end Chain

/-! ## The batching's honest hints -/

section Batch

theorem isTotalQueryBound_obsAllHM : ∀ (cv : Digest) (xs : List E),
    IsTotalQueryBound (obsAllHM queryH cv xs) xs.length
  | _, [] => trivial
  | cv, x :: xs => by
    simp only [obsAllHM, List.foldlM_cons, List.length_cons]
    exact isTotalQueryBound_queryH_bind _ fun d ↦ isTotalQueryBound_obsAllHM d xs

theorem isTotalQueryBound_sq2HM : ∀ (n : ℕ) (cv : Digest),
    IsTotalQueryBound (sq2HM queryH n cv) (2 * n)
  | 0, _ => trivial
  | n + 1, cv => by
    simp only [sq2HM]
    rw [show 2 * (n + 1) = (2 * n + 0) + 1 + 1 by ring]
    exact isTotalQueryBound_queryH_bind _ fun _ ↦ isTotalQueryBound_queryH_bind _ fun _ ↦
      isTotalQueryBound_bind (n₂ := 0) (isTotalQueryBound_sq2HM n _) fun _ ↦ trivial

theorem isTotalQueryBound_sq3HM : ∀ (n : ℕ) (cv : Digest),
    IsTotalQueryBound (sq3HM queryH n cv) (3 * n)
  | 0, _ => trivial
  | n + 1, cv => by
    simp only [sq3HM]
    rw [show 3 * (n + 1) = (3 * n + 0) + 1 + 1 + 1 by ring]
    exact isTotalQueryBound_queryH_bind _ fun _ ↦ isTotalQueryBound_queryH_bind _ fun _ ↦
      isTotalQueryBound_queryH_bind _ fun _ ↦
        isTotalQueryBound_bind (n₂ := 0) (isTotalQueryBound_sq3HM n _) fun _ ↦ trivial

theorem isTotalQueryBound_roundCvM (cv : Digest) (msg : E × E) :
    IsTotalQueryBound (roundCvM queryH cv msg) 3 :=
  isTotalQueryBound_queryH_bind (n := 2) _ fun _ ↦ isTotalQueryBound_queryH_bind _ fun _ ↦
    isTotalQueryBound_queryH_one _

theorem isTotalQueryBound_honestRoundsM (n : ℕ) (f : List E → E) :
    ∀ (k : ℕ) (pre : List E) (cv : Digest),
      IsTotalQueryBound (honestRoundsM queryH n f k pre cv) (3 * k)
  | 0, _, _ => trivial
  | k + 1, pre, cv => by
    simp only [honestRoundsM]
    rw [show 3 * (k + 1) = 3 + (3 * k + 0) by ring]
    exact isTotalQueryBound_bind (isTotalQueryBound_roundCvM _ _) fun _ ↦
      isTotalQueryBound_bind (isTotalQueryBound_honestRoundsM n f k _ _) fun _ ↦ trivial

theorem length_of_mem_support_honestRoundsM (n : ℕ) (f : List E → E) :
    ∀ (k : ℕ) (pre : List E) (cv : Digest) (r : List (E × E)),
      r ∈ support (honestRoundsM queryH n f k pre cv) → r.length = k
  | 0, _, _, r, hr => by simp [honestRoundsM] at hr; simp [hr]
  | k + 1, pre, cv, r, hr => by
    simp only [honestRoundsM, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hr
    obtain ⟨cv', -, rest, hrest, rfl⟩ := hr
    simp [length_of_mem_support_honestRoundsM n f k _ _ rest hrest]

/-- The batching's honest hints' queries: the children's cells and the bytecode's lambdas,
its honest rounds twice (their messages' chain, then the sumcheck), the matrices' lambdas and
zero rounds. -/
def honestBatchQueries (bytecode : List K) (cs : List ChildClaims) : ℕ :=
  1 + (cs.flatMap childCells).length + 5 * cs.length + 6 * Nat.log2 bytecode.length +
    6 * blake2sR1csLogSize

/-- **The batching's honest hints' queries.** -/
theorem isTotalQueryBound_honestBatchM (s0 : Digest) (bytecode : List K)
    (cs : List ChildClaims) :
    IsTotalQueryBound (honestBatchM queryH s0 bytecode cs) (honestBatchQueries bytecode cs) := by
  unfold honestBatchM
  refine (isTotalQueryBound_bind (isTotalQueryBound_obsAllHM s0 _) fun cvA ↦
    isTotalQueryBound_bind (isTotalQueryBound_sq2HM cs.length cvA) fun b ↦
      isTotalQueryBound_bind_of_mem_support (isTotalQueryBound_honestRoundsM _ _ _ _ _)
        (suffixBound := 3 * Nat.log2 bytecode.length + (3 * cs.length +
          (3 * (2 * blake2sR1csLogSize) + 0))) fun rounds hr ↦ ?_).mono ?_
  · have hlen := length_of_mem_support_honestRoundsM _ _ _ _ _ rounds hr
    refine isTotalQueryBound_bind ((costS_batchRoundsWith _ rounds b.2).mono (by rw [hlen]))
      fun be ↦ isTotalQueryBound_bind (isTotalQueryBound_sq3HM cs.length be.2) fun ms ↦
        isTotalQueryBound_bind ((costS_batchRoundsWith _ zeroRounds ms.2).mono
          (by simp [zeroRounds])) fun _ ↦ trivial
  · simp only [honestBatchQueries, List.length_cons]
    omega

end Batch

/-! ## The node's checks -/

section Node

/-- The deferring verifier makes its seed's query and its program's. -/
theorem isTotalQueryBound_verifyDeferredWith (bytecode : List K) (iv pi : Digest)
    (c : FixedClaims) (π : Proof) :
    IsTotalQueryBound (verifyDeferredWith queryH bytecode iv pi c π) (1 + leanVmCost) := by
  unfold verifyDeferredWith
  rw [Nat.add_comm]
  exact isTotalQueryBound_queryH_bind _ fun seed ↦
    isTotalQueryBound_runProof (costLE_deferredProgram c bytecode pi) seed π

/-- A child's checks. -/
theorem isTotalQueryBound_childChecksWith (bytecode : List K) (seed : Digest) (c : Child) :
    IsTotalQueryBound (childChecksWith queryH bytecode seed c) (6 + leanVmCost) := by
  unfold childChecksWith
  rw [show 6 + leanVmCost = 5 + ((1 + leanVmCost) + 0) by omega]
  exact isTotalQueryBound_bind (isTotalQueryBound_statementDigestWith _ _) fun pi ↦
    isTotalQueryBound_bind (isTotalQueryBound_verifyDeferredWith _ _ _ _ _) fun _ ↦ trivial

theorem isTotalQueryBound_childrenChecksWith (bytecode : List K) (seed : Digest) :
    ∀ cs : List Child,
      IsTotalQueryBound (childrenChecksWith queryH bytecode seed cs) (cs.length * (6 + leanVmCost))
  | [] => trivial
  | c :: cs => by
    simp only [childrenChecksWith, List.length_cons]
    rw [Nat.add_mul, one_mul, Nat.add_comm]
    exact isTotalQueryBound_bind (isTotalQueryBound_childChecksWith _ _ c) fun _ ↦
      isTotalQueryBound_childrenChecksWith bytecode seed cs

/-- The holders' checks' bound: `g` of every claim held directly. -/
def holdersQueries {α W : Type} (g : α → W → ℕ) (as : List α) (hs : List (Holder W)) : ℕ :=
  ((Hints.direct as hs).map fun p ↦ g p.1 p.2).sum

theorem isTotalQueryBound_holdersChecksWith {α W : Type} (f : α → W → OracleComp HashSpec Unit)
    (g : α → W → ℕ) (hf : ∀ a w, IsTotalQueryBound (f a w) (g a w)) :
    ∀ (as : List α) (hs : List (Holder W)),
      IsTotalQueryBound (holdersChecksWith f as hs) (holdersQueries g as hs)
  | a :: as, .direct w :: hs => by
    simp only [holdersChecksWith, holderChecksWith, holdersQueries, Hints.direct, List.map_cons,
      List.sum_cons]
    exact isTotalQueryBound_bind (hf a w) fun _ ↦
      isTotalQueryBound_holdersChecksWith f g hf as hs
  | a :: as, .child _ :: hs => by
    simp only [holdersChecksWith, holderChecksWith, holdersQueries, Hints.direct, pure_bind]
    exact isTotalQueryBound_holdersChecksWith f g hf as hs
  | [], _ => trivial
  | _ :: _, [] => trivial

theorem isTotalQueryBound_xmssCheckWith (c : XmssClaim) (σ : LeanXmss.Signature) :
    IsTotalQueryBound (xmssCheckWith queryH c σ) xmssVerifyBound := by
  unfold xmssCheckWith
  rw [← Nat.add_zero xmssVerifyBound]
  refine isTotalQueryBound_bind ?_ fun _ ↦ trivial
  rw [xmssVerifyWith_eq_simulateQ]
  exact IsTotalQueryBound.simulateQ_of_step (verify_isTotalQueryBound _ _ _) fun t ↦
    isTotalQueryBound_map_of _ (isTotalQueryBound_queryH_one t)

theorem isTotalQueryBound_sphincsCheckWith (c : SphincsClaim) (σ : Sphincs.Signature) :
    IsTotalQueryBound (sphincsCheckWith queryH c σ) sphincsVerifyBound := by
  unfold sphincsCheckWith
  rw [← Nat.add_zero sphincsVerifyBound]
  refine isTotalQueryBound_bind ?_ fun _ ↦ trivial
  rw [sphincsVerifyWith_eq_simulateQ]
  exact IsTotalQueryBound.simulateQ_of_step (sphincsVerify_isTotalQueryBound _ _ _) fun t ↦
    isTotalQueryBound_map_of _ (isTotalQueryBound_queryH_one t)

/-! ### The DA opening -/

section Da

variable (HD : List UInt8 → OracleComp HashSpec LeanDa.Digest)
  (hHD : ∀ x, IsTotalQueryBound (HD x) 1)
include hHD

theorem isTotalQueryBound_treeLevelWith (nodes : List LeanDa.Digest) :
    IsTotalQueryBound (Da.treeLevelWith HD nodes) (nodes.length / 2) := by
  unfold Da.treeLevelWith
  simpa using isTotalQueryBound_mapM _ 1 (fun _ ↦ hHD _) (List.range (nodes.length / 2))

omit hHD in
theorem length_of_mem_support_treeLevelWith (nodes : List LeanDa.Digest) (x : List LeanDa.Digest)
    (hx : x ∈ support (Da.treeLevelWith HD nodes)) : x.length = nodes.length / 2 := by
  unfold Da.treeLevelWith at hx
  simpa using length_of_mem_support_mapM _ _ x hx

/-- A tree's root makes at most as many queries as it has leaves. -/
theorem isTotalQueryBound_treeRootFuel :
    ∀ (fuel : ℕ) (nodes : List LeanDa.Digest),
      IsTotalQueryBound (Da.treeRootFuel HD fuel nodes) nodes.length
  | 0, _ => trivial
  | fuel + 1, nodes => by
    simp only [Da.treeRootFuel]
    split
    · trivial
    · refine (isTotalQueryBound_bind_of_mem_support (isTotalQueryBound_treeLevelWith HD hHD nodes)
        (suffixBound := nodes.length / 2) fun next hnext ↦
          (isTotalQueryBound_treeRootFuel fuel next).mono
            (length_of_mem_support_treeLevelWith HD nodes next hnext).le).mono ?_
      omega

theorem isTotalQueryBound_rowDigestWith (row : List K) :
    IsTotalQueryBound (Da.rowDigestWith HD row) (LeanDa.payloadCells + 1) := by
  unfold Da.rowDigestWith
  refine isTotalQueryBound_bind ?_ fun _ ↦ hHD _
  have h := isTotalQueryBound_mapM (fun j ↦ Da.listCellDigestWith HD row j) 1 (fun _ ↦ hHD _)
    (List.range LeanDa.payloadCells)
  rwa [List.length_range, Nat.mul_one] at h

/-- The DA commitment's queries at `r` rows: the rows' digests, the rows' tree, the columns'
cells (at most `cellsPerRow · nPad r`) and tree, and the root. -/
def daCommitQueries (r : ℕ) : ℕ :=
  r * (LeanDa.payloadCells + 1) + (r + (LeanDa.nPad r - r)) +
    2 * (LeanDa.cellsPerRow * LeanDa.nPad r) + 1

theorem isTotalQueryBound_commitCodewordsWith (pc pr : LeanDa.Digest) (rows : List (List K)) :
    IsTotalQueryBound (Da.commitCodewordsWith HD pc pr rows) (daCommitQueries rows.length) := by
  unfold Da.commitCodewordsWith Da.treeRootWith daCommitQueries
  have hcols : ((List.range LeanDa.cellsPerRow).flatMap fun j ↦
      (List.range (LeanDa.nPad rows.length)).map fun i ↦ (i, j)).length =
        LeanDa.cellsPerRow * LeanDa.nPad rows.length := by
    simp [List.length_flatMap, List.sum_replicate]
  refine (isTotalQueryBound_bind_of_mem_support (isTotalQueryBound_mapM _ _
    (isTotalQueryBound_rowDigestWith HD hHD) rows)
    (suffixBound := (rows.length + (LeanDa.nPad rows.length - rows.length)) +
      (LeanDa.cellsPerRow * LeanDa.nPad rows.length +
        (LeanDa.cellsPerRow * LeanDa.nPad rows.length + 1))) fun rds hrds ↦ ?_).mono ?_
  · have hl := length_of_mem_support_mapM _ _ rds hrds
    refine isTotalQueryBound_bind ((isTotalQueryBound_treeRootFuel HD hHD _ _).mono
      (by simp [hl])) fun _ ↦ ?_
    refine isTotalQueryBound_bind_of_mem_support ((isTotalQueryBound_mapM _ 1 (fun ij ↦ ?_) _).mono
      (by rw [hcols, Nat.mul_one]))
      (suffixBound := LeanDa.cellsPerRow * LeanDa.nPad rows.length + 1) fun cols hc ↦ ?_
    · split
      · exact hHD _
      · trivial
    · have hcl := length_of_mem_support_mapM _ _ cols hc
      rw [hcols] at hcl
      exact isTotalQueryBound_bind ((isTotalQueryBound_treeRootFuel HD hHD _ _).mono
        (by rw [hcl])) fun _ ↦ hHD _
  · omega

end Da

/-- The hash of DA digests makes one query. -/
theorem isTotalQueryBound_daHash (x : List UInt8) : IsTotalQueryBound (Da.daHash queryH x) 1 :=
  isTotalQueryBound_map_of _ (isTotalQueryBound_queryH_one x)

/-- A DA opening's queries at `r` rows: the commitment and the vector digest. -/
def daQueries (r : ℕ) : ℕ := daCommitQueries r + 1

theorem isTotalQueryBound_daCheckWith (pc pr : LeanDa.Digest) (c : DaClaim) (w : Da.Witness) :
    IsTotalQueryBound (daCheckWith queryH pc pr c w) (daQueries w.rows.length) := by
  unfold daCheckWith daQueries
  rw [show daCommitQueries w.rows.length + 1 = daCommitQueries w.rows.length + (1 + 0) by omega]
  exact isTotalQueryBound_bind (isTotalQueryBound_commitCodewordsWith _ isTotalQueryBound_daHash
    _ _ _) fun _ ↦ isTotalQueryBound_bind (isTotalQueryBound_daHash _) fun _ ↦ trivial

/-! ### The children's claims and the batching -/

theorem isTotalQueryBound_childClaimsM (seed : Digest) (children : List Child) :
    IsTotalQueryBound (childClaimsM queryH seed children) (children.length * 5) :=
  isTotalQueryBound_mapM _ 5
    (fun _ ↦ isTotalQueryBound_map_of _ (isTotalQueryBound_statementDigestWith _ _)) _

/-- The children's claims are the children's fresh claims and deferred claims, with some public
inputs. -/
theorem fst_of_mem_support_childClaimsM (seed : Digest) :
    ∀ (children : List Child) (ccs : List ChildClaims),
      ccs ∈ support (childClaimsM queryH seed children) →
      ccs.map (fun c ↦ (c.fresh, c.carried)) = children.map fun c ↦ (c.fresh, c.statement.defer)
  | [], ccs, h => by simp [childClaimsM] at h; simp [h]
  | c :: cs, ccs, h => by
    simp only [childClaimsM, List.mapM_cons, mem_support_bind_iff, support_map, Set.mem_image,
      support_pure, Set.mem_singleton_iff] at h
    obtain ⟨cc, ⟨pi, -, rfl⟩, rest, hrest, rfl⟩ := h
    simp only [List.map_cons, List.cons.injEq, true_and]
    exact fst_of_mem_support_childClaimsM seed cs rest hrest

/-- A batching's queries: the children's count and cells, their lambdas, the two sumchecks. -/
def batchQueries (cs : List ChildClaims) (h : BatchHints) : ℕ :=
  1 + (cs.map fun c ↦ 2 + (fixedCells c.fresh ++ c.carried.cells).length).sum + 2 * cs.length +
    3 * h.bytecodeRounds.length + 3 * cs.length + 3 * h.matrixRounds.length

/-- **A batching's queries.** -/
theorem isTotalQueryBound_batchWith (s0 : Digest) (cs : List ChildClaims) (h : BatchHints) :
    IsTotalQueryBound (batchWith queryH s0 cs h) (batchQueries cs h) := by
  have hgo : CostS (batchWith.go queryH cs h) (batchQueries cs h) := by
    unfold batchWith.go
    refine (costS_bind (costS_observe _) fun _ ↦ costS_bind
      (costS_forIn _ (fun c : ChildClaims ↦ 2 + (fixedCells c.fresh ++ c.carried.cells).length)
        (fun c _ ↦
        (costS_bind (costS_observe _) fun _ ↦ costS_bind (costS_observe _) fun _ ↦
          costS_bind (costS_forIn _ (fun _ ↦ 1) (fun _ _ ↦ (costS_bind (costS_observe _) fun _ ↦
            costS_pure _).mono le_rfl) _ _) fun _ ↦ costS_pure _).mono (by simp; omega)) _ _)
      fun _ ↦ costS_bind (costS_forIn _ (fun _ ↦ 2) (fun _ _ ↦ costS_bind costS_squeeze fun _ ↦
        costS_bind costS_squeeze fun _ ↦ costS_pure _) _ _) fun _ ↦
        costS_bind (b := (cs.map fun _ ↦ 3).sum + (3 * h.matrixRounds.length + 0))
          (costS_batchRoundsWith _ _) fun p ↦ ?_).mono ?_
    · obtain ⟨rB, fB⟩ := p
      refine costS_bind (costS_forIn _ (fun _ ↦ 3) (fun _ _ ↦ costS_bind costS_squeeze fun _ ↦
        costS_bind costS_squeeze fun _ ↦ costS_bind costS_squeeze fun _ ↦ costS_pure _) _ _)
          fun _ ↦ costS_bind (costS_batchRoundsWith _ _) fun q ↦ ?_
      obtain ⟨rM, fM⟩ := q
      dsimp only
      split
      · exact costS_pure _
      · exact costS_pure _
    · simp only [batchQueries, List.map_const', List.sum_replicate, smul_eq_mul]
      omega
  exact isTotalQueryBound_map_of _ (hgo s0)

/-! ### The node's checks and their log -/

/-- **The node's checks' queries**, as a function of the statement and the witness. -/
def nodeChecksQueries (s : NodeStatement) (w : NodeWitness) : ℕ :=
  5 + w.children.length * (6 + leanVmCost) +
    holdersQueries (fun _ _ ↦ xmssVerifyBound) s.claims.xmss w.xmss +
    holdersQueries (fun _ _ ↦ sphincsVerifyBound) s.claims.sphincs w.sphincs +
    holdersQueries (fun (_ : DaClaim) (dw : Da.Witness) ↦ daQueries dw.rows.length) s.claims.da
      w.da +
    w.children.length * 5 +
    (1 + (w.children.map fun c ↦ 2 + (fixedCells c.fresh ++ c.statement.defer.cells).length).sum +
      2 * w.children.length + 3 * w.hints.bytecodeRounds.length + 3 * w.children.length +
      3 * w.hints.matrixRounds.length)

/-- **The node's checks' queries.** -/
theorem isTotalQueryBound_nodeChecksWith (s0 : Digest) (pc pr : LeanDa.Digest)
    (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    IsTotalQueryBound (nodeChecksWith queryH s0 pc pr bytecode seed s w)
      (nodeChecksQueries s w) := by
  unfold nodeChecksWith
  refine (isTotalQueryBound_bind (isTotalQueryBound_statementDigestWith _ _) fun _ ↦
    isTotalQueryBound_bind (isTotalQueryBound_childrenChecksWith _ _ _) fun _ ↦
    isTotalQueryBound_bind (isTotalQueryBound_holdersChecksWith _ _
      isTotalQueryBound_xmssCheckWith _ _) fun _ ↦
    isTotalQueryBound_bind (isTotalQueryBound_holdersChecksWith _ _
      isTotalQueryBound_sphincsCheckWith _ _) fun _ ↦
    isTotalQueryBound_bind (isTotalQueryBound_holdersChecksWith _ _
      (isTotalQueryBound_daCheckWith pc pr) _ _) fun _ ↦
    isTotalQueryBound_bind_of_mem_support (isTotalQueryBound_childClaimsM _ _)
      (suffixBound := 1 + (w.children.map fun c ↦
        2 + (fixedCells c.fresh ++ c.statement.defer.cells).length).sum +
        2 * w.children.length + 3 * w.hints.bytecodeRounds.length + 3 * w.children.length +
        3 * w.hints.matrixRounds.length + 0) fun ccs hccs ↦ ?_).mono ?_
  · have hm := fst_of_mem_support_childClaimsM seed w.children ccs hccs
    have hlen : ccs.length = w.children.length := by
      simpa using congrArg List.length hm
    have hsum : (ccs.map fun c ↦ 2 + (fixedCells c.fresh ++ c.carried.cells).length).sum =
        (w.children.map fun c ↦
          2 + (fixedCells c.fresh ++ c.statement.defer.cells).length).sum := by
      have := congrArg (fun l ↦ (l.map fun p ↦ 2 + (fixedCells p.1 ++ p.2.cells).length).sum) hm
      simpa only [List.map_map, Function.comp_def] using this
    refine isTotalQueryBound_bind ((isTotalQueryBound_batchWith s0 ccs w.hints).mono ?_) fun _ ↦
      (trivial : IsTotalQueryBound (pure () : OracleComp HashSpec Unit) 0)
    simp only [batchQueries, hlen, hsum, le_refl]
  · simp only [nodeChecksQueries]
    omega

/-- The logging hash's implementation of the oracle. -/
def logImpl : QueryImpl HashSpec (StateT Log (OracleComp HashSpec)) :=
  fun x ↦ logHashM queryH x

/-- **The node's logged checks' queries**: the checks'. -/
theorem isTotalQueryBound_nodeLogPairsWithM (s0 : Digest) (pc pr : LeanDa.Digest)
    (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    IsTotalQueryBound (nodeLogPairsWithM queryH s0 pc pr bytecode seed s w)
      (nodeChecksQueries s w) := by
  have h := rel_nodeChecksWith (m := StateT Log (OracleComp HashSpec)) (n := OracleComp HashSpec)
    (fun x y ↦ x = simulateQ logImpl y) (fun a ↦ (simulateQ_pure _ a).symm)
    (fun x y f g hxy hfg ↦ by
      rw [simulateQ_bind, hxy]
      exact congrArg _ (funext hfg))
    (logHashM queryH) queryH (fun x ↦ (simulateQ_queryH logImpl x).symm) s0 pc pr bytecode seed s w
  unfold nodeLogPairsWithM
  rw [h]
  refine isTotalQueryBound_map_of _ (IsTotalQueryBound.simulateQ_run_of_step
    (isTotalQueryBound_nodeChecksWith s0 pc pr bytecode seed s w) (fun t ℓ ↦ ?_) [])
  simp only [logImpl, logHashM, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    bind_pure_comp]
  exact isTotalQueryBound_bind (n₂ := 0)
    (isTotalQueryBound_map_of _ (isTotalQueryBound_queryH_one t))
    fun _ ↦ trivial

/-- **The node's log's queries**, from the IV. -/
theorem isTotalQueryBound_nodeLogPairsM (s : NodeStatement) (w : NodeWitness) :
    IsTotalQueryBound (nodeLogPairsM queryH s w) (2 + nodeChecksQueries s w) :=
  isTotalQueryBound_bind isTotalQueryBound_seedOfM fun _ ↦
    isTotalQueryBound_nodeLogPairsWithM _ _ _ _ _ s w

/-! ### The closed bound -/

theorem holdersQueries_le {α W : Type} (g : α → W → ℕ) (M : ℕ) :
    ∀ (as : List α) (hs : List (Holder W)), (∀ w, Holder.direct w ∈ hs → ∀ a, g a w ≤ M) →
      holdersQueries g as hs ≤ (Hints.direct as hs).length * M
  | a :: as, .direct w :: hs, h => by
    have ih := holdersQueries_le g M as hs fun w' hw' ↦ h w' (List.mem_cons_of_mem _ hw')
    simp only [holdersQueries, Hints.direct, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    have := h w List.mem_cons_self a
    rw [Nat.add_mul, one_mul]
    omega
  | a :: as, .child _ :: hs, h => by
    have ih := holdersQueries_le g M as hs fun w' hw' ↦ h w' (List.mem_cons_of_mem _ hw')
    simpa only [holdersQueries, Hints.direct] using ih
  | [], _, _ => by simp [holdersQueries, Hints.direct]
  | _ :: _, [], _ => by simp [holdersQueries, Hints.direct]

theorem length_direct_le {α W : Type} :
    ∀ (as : List α) (hs : List (Holder W)), (Hints.direct as hs).length ≤ as.length
  | a :: as, .direct w :: hs => by
    simp only [Hints.direct, List.length_cons]
    have := length_direct_le as hs
    omega
  | a :: as, .child _ :: hs => by
    simp only [Hints.direct, List.length_cons]
    have := length_direct_le as hs
    omega
  | [], _ => by simp [Hints.direct]
  | _ :: _, [] => by simp [Hints.direct]

theorem sum_map_le_mul {α : Type} (f : α → ℕ) (K : ℕ) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ K) → (l.map f).sum ≤ l.length * K
  | [], _ => by simp
  | a :: l, h => by
    have ih := sum_map_le_mul f K l fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    have := h a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
    omega

/-- The padded row count at most `LeanDa.maxRows` rows. -/
theorem nPad_le_maxRows {r : ℕ} (hr : r ≤ LeanDa.maxRows) : LeanDa.nPad r ≤ 1024 := by
  have h : LeanDa.nPad LeanDa.maxRows = 1024 := by
    show 2 ^ Nat.clog 2 1024 = 1024
    rw [show (1024 : ℕ) = 2 ^ 10 by norm_num, Nat.clog_pow 2 10 (by norm_num)]
  rw [← h]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.clog_mono_right 2 hr)

/-- A DA opening's queries at most `LeanDa.maxRows` rows. -/
theorem daQueries_le {r : ℕ} (hr : r ≤ LeanDa.maxRows) : daQueries r ≤ 329730 := by
  have h := nPad_le_maxRows hr
  have hr' : r ≤ 1024 := hr
  unfold daQueries daCommitQueries
  simp only [LeanDa.payloadCells, LeanDa.cellsPerRow]
  omega

/-- The bytecode point's length. -/
theorem log2_bytecode_length_eq : Nat.log2 End.bytecode.length = 22 :=
  (congrArg Nat.log2 End.bytecode_length).trans Nat.log2_two_pow

/-- **The closed bound on a node's checks**: sixteen children, `2^16` signatures, one DA opening
of at most `LeanDa.maxRows` rows, the batching of sixteen shaped children. -/
def nodeChecksBound : ℕ :=
  5 + 16 * (6 + leanVmCost) + sphincsVerifyBound * 2 ^ 16 + 329730 + 16 * 5 +
    (1 + 16 * childLen 22 + 5 * 16 + 3 * 22 + 3 * (2 * blake2sR1csLogSize))

/-- The closed bound's value. -/
theorem nodeChecksBound_eq : nodeChecksBound = 45501774 := by decide

/-- **The node's checks' queries, bounded**: under the deployed limits, DA openings of at most
`LeanDa.maxRows` rows, children of `childLen` cells and the honest hints' round counts. -/
theorem nodeChecksQueries_le {s : NodeStatement} {w : NodeWitness} (hlim : End.Limits s w)
    (hda : ∀ dw, Holder.direct dw ∈ w.da → dw.rows.length ≤ LeanDa.maxRows)
    (hcells : ∀ c ∈ w.children, ∀ pi : Digest,
      (childCells ⟨pi, c.fresh, c.statement.defer⟩).length =
        childLen (Nat.log2 End.bytecode.length))
    (hb : w.hints.bytecodeRounds.length = Nat.log2 End.bytecode.length)
    (hm : w.hints.matrixRounds = zeroRounds) :
    nodeChecksQueries s w ≤ nodeChecksBound := by
  have hch := hlim.children
  have hcov := hlim.coverage
  have hdir := hlim.directDa
  have hcv : s.claims.xmss.length + s.claims.sphincs.length ≤ End.coverage s w := by
    unfold End.coverage
    dsimp only
    omega
  have hx := holdersQueries_le (fun (_ : XmssClaim) (_ : LeanXmss.Signature) ↦ xmssVerifyBound)
    sphincsVerifyBound s.claims.xmss w.xmss fun _ _ _ ↦ by decide
  have hs := holdersQueries_le (fun (_ : SphincsClaim) (_ : Sphincs.Signature) ↦ sphincsVerifyBound)
    sphincsVerifyBound s.claims.sphincs w.sphincs fun _ _ _ ↦ le_rfl
  have hd := holdersQueries_le (fun (_ : DaClaim) (dw : Da.Witness) ↦ daQueries dw.rows.length)
    329730 s.claims.da w.da fun dw hdw _ ↦ daQueries_le (hda dw hdw)
  have hlx := length_direct_le s.claims.xmss w.xmss
  have hls := length_direct_le s.claims.sphincs w.sphincs
  have hsum := sum_map_le_mul
    (fun c : Child ↦ 2 + (fixedCells c.fresh ++ c.statement.defer.cells).length)
    (childLen 22) w.children fun c hc ↦ by
      have := hcells c hc 0
      rw [log2_bytecode_length_eq] at this
      simp only [childCells, List.length_append, List.length_cons, List.length_nil] at this ⊢
      omega
  have hmr : w.hints.matrixRounds.length = 2 * blake2sR1csLogSize := by
    rw [hm]
    simp [zeroRounds]
  rw [log2_bytecode_length_eq] at hb
  have hxy : (Hints.direct s.claims.xmss w.xmss).length * sphincsVerifyBound +
      (Hints.direct s.claims.sphincs w.sphincs).length * sphincsVerifyBound ≤
        sphincsVerifyBound * 2 ^ 16 := by
    rw [← Nat.add_mul, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  have h16 : w.children.length * (6 + leanVmCost) ≤ 16 * (6 + leanVmCost) :=
    Nat.mul_le_mul_right _ hch
  have h16' : w.children.length * childLen 22 ≤ 16 * childLen 22 := Nat.mul_le_mul_right _ hch
  have hdd : (Hints.direct s.claims.da w.da).length * 329730 ≤ 329730 := by
    have := Nat.mul_le_mul_right 329730 hdir
    omega
  unfold nodeChecksQueries nodeChecksBound
  rw [hb, hmr]
  omega

/-- **The node's log's queries, bounded.** -/
theorem isTotalQueryBound_nodeLogPairsM_le {s : NodeStatement} {w : NodeWitness}
    (hlim : End.Limits s w)
    (hda : ∀ dw, Holder.direct dw ∈ w.da → dw.rows.length ≤ LeanDa.maxRows)
    (hcells : ∀ c ∈ w.children, ∀ pi : Digest,
      (childCells ⟨pi, c.fresh, c.statement.defer⟩).length =
        childLen (Nat.log2 End.bytecode.length))
    (hb : w.hints.bytecodeRounds.length = Nat.log2 End.bytecode.length)
    (hm : w.hints.matrixRounds = zeroRounds) :
    IsTotalQueryBound (nodeLogPairsM queryH s w) (2 + nodeChecksBound) :=
  (isTotalQueryBound_nodeLogPairsM s w).mono
    (Nat.add_le_add_left (nodeChecksQueries_le hlim hda hcells hb hm) 2)

end Node

end
end LeanVM.E2E.Complete
