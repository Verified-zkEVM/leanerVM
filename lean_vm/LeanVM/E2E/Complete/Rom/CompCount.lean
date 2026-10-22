/-
  LeanVM.E2E.Complete.Rom.CompCount

  T6-prob: the queries of the honest prover of the random-oracle model, a function of the tree
  alone, and their closed bound per node under a shape condition.
-/

module

public import LeanVM.E2E.Complete.Rom.Comp
public import LeanVM.E2E.Complete.Rom.CountM
public import LeanVM.E2E.Complete.Rom.Kids
public import LeanVM.Protocol.EndToEnd.Blind.Cost
public import LeanVM.Protocol.Verifier.DeferredShape

/-!
# The honest prover's queries

`docs/roadmap/t6-prob.md` §4.4. `honestProverComp ρ pfuel T` makes at most
`T.proverQueries ρ pfuel` queries (`isTotalQueryBound_honestProverComp`), a function of the tree
alone: per node, the children's digests, the batching (`honestBatchM`, `batchWith`), the statement's
digest, the node's logged checks (`nodeLogPairsM`), the seed, V°'s proof (`proveM`,
`costLE_blindProgram`), the fresh claims' run (`freshRunM`) and the children's digests again.

The counts read the children's claims only through their shapes, which every output of the prover
has (`outShapedN_of_mem_support`): the fresh claims are a return of `claimsProg`, V°'s prefix
(`freshShapedFor_of_returns_claimsProg`, read off every run: `returns_of_mem_support_fsRunM`), and
the deferred claim is a leaf's or one whose bytecode part holds. The honest rounds are
`Nat.log2 End.bytecode.length` (`honestRoundsM`) and the matrices' rounds `zeroRounds`.

Under `HonestTree.ShapeOK` (at most sixteen children, `2^16` signature claims, one direct DA
opening of at most `LeanDa.maxRows` rows) a node costs at most `nodeQueries pfuel`
(`proverQueries_le`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Guest.Batch LeanVM.Guest.B1.Main LeanVM.E2E LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.EndToEnd OracleComp OracleSpec

@[expose] public section

/-! ## Computations in `ExceptT` -/

section ExceptTCount

variable {ε : Type}

local notation "OC" => OracleComp HashSpec

theorem isTotalQueryBound_exceptT_bind {α β : Type} {x : ExceptT ε OC α}
    {f : α → ExceptT ε OC β} {n₁ n₂ : ℕ} (hx : IsTotalQueryBound x.run n₁)
    (hf : ∀ a, Except.ok a ∈ support x.run → IsTotalQueryBound (f a).run n₂) :
    IsTotalQueryBound (x >>= f).run (n₁ + n₂) := by
  rw [ExceptT.run_bind]
  refine isTotalQueryBound_bind_of_mem_support hx fun r hr ↦ ?_
  cases r with
  | error e => exact isTotalQueryBound_pure' _ _
  | ok a => exact hf a hr

theorem mem_support_exceptT_bind {α β : Type} {x : ExceptT ε OC α} {f : α → ExceptT ε OC β}
    {b : β} (h : Except.ok b ∈ support (x >>= f).run) :
    ∃ a, Except.ok a ∈ support x.run ∧ Except.ok b ∈ support (f a).run := by
  rw [ExceptT.run_bind, mem_support_bind_iff] at h
  obtain ⟨r, hr, h⟩ := h
  cases r with
  | error e =>
    change Except.ok b ∈ support (pure (Except.error e) : OC (Except ε β)) at h
    simp at h
  | ok a => exact ⟨a, hr, h⟩

theorem run_monadLift_exceptT {α : Type} (x : OC α) :
    (monadLift x : ExceptT ε OC α).run = Except.ok <$> x := by
  simp

theorem isTotalQueryBound_exceptT_lift {α : Type} {x : OC α} {n : ℕ}
    (h : IsTotalQueryBound x n) : IsTotalQueryBound (monadLift x : ExceptT ε OC α).run n := by
  rw [run_monadLift_exceptT]
  exact isTotalQueryBound_map_of _ h

theorem mem_support_exceptT_lift {α : Type} {x : OC α} {a : α}
    (h : Except.ok a ∈ support (monadLift x : ExceptT ε OC α).run) : a ∈ support x := by
  rw [run_monadLift_exceptT, support_map] at h
  obtain ⟨a', ha', he⟩ := h
  cases he
  exact ha'

theorem isTotalQueryBound_exceptT_pure {α : Type} (a : α) (n : ℕ) :
    IsTotalQueryBound (pure a : ExceptT ε OC α).run n :=
  isTotalQueryBound_pure' _ n

theorem isTotalQueryBound_exceptT_throw {α : Type} (e : ε) (n : ℕ) :
    IsTotalQueryBound (throw e : ExceptT ε OC α).run n :=
  isTotalQueryBound_pure' _ n

theorem mem_support_exceptT_pure {α : Type} {a b : α}
    (h : Except.ok b ∈ support (pure a : ExceptT ε OC α).run) : b = a := by
  change Except.ok b ∈ support (pure (Except.ok a) : OC (Except ε α)) at h
  simpa using h

theorem not_mem_support_exceptT_throw {α : Type} {e : ε} {b : α}
    (h : Except.ok b ∈ support (throw e : ExceptT ε OC α).run) : False := by
  change Except.ok b ∈ support (pure (Except.error e) : OC (Except ε α)) at h
  simp at h

/-- **A `mapM`'s queries in `ExceptT`**: the sum of the elements'. -/
theorem isTotalQueryBound_exceptT_mapM {α β : Type} (f : α → ExceptT ε OC β) (g : α → ℕ) :
    ∀ l : List α, (∀ a ∈ l, IsTotalQueryBound (f a).run (g a)) →
      IsTotalQueryBound (l.mapM f).run (l.map g).sum
  | [], _ => isTotalQueryBound_pure' _ _
  | a :: l, h => by
    rw [List.mapM_cons, List.map_cons, List.sum_cons, ← Nat.add_zero (List.sum _)]
    exact isTotalQueryBound_exceptT_bind (h a List.mem_cons_self) fun _ _ ↦
      isTotalQueryBound_exceptT_bind (isTotalQueryBound_exceptT_mapM f g l
        fun b hb ↦ h b (List.mem_cons_of_mem _ hb)) fun _ _ ↦ isTotalQueryBound_exceptT_pure _ _

/-- **A `mapM`'s values in `ExceptT`**: elementwise values of the function. -/
theorem forall₂_of_mem_support_exceptT_mapM {α β : Type} (f : α → ExceptT ε OC β) :
    ∀ (l : List α) (bs : List β), Except.ok bs ∈ support (l.mapM f).run →
      List.Forall₂ (fun a b ↦ Except.ok b ∈ support (f a).run) l bs
  | [], bs, h => by
    rw [List.mapM_nil] at h
    rw [mem_support_exceptT_pure h]
    exact .nil
  | a :: l, bs, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := mem_support_exceptT_bind h
    obtain ⟨bs', hbs', h⟩ := mem_support_exceptT_bind h
    rw [mem_support_exceptT_pure h]
    exact .cons hb (forall₂_of_mem_support_exceptT_mapM f l bs' hbs')

end ExceptTCount

/-! ## The shapes of the fresh claims -/

section FreshShape

/-- A run's return is a return of its program. -/
theorem returns_of_mem_support_fsRunM (S : Strategy) (fuel : ℕ) {α : Type} :
    ∀ (p : Prog α) (cv : Digest) (h : List Ev) (r : α × Digest × List Ev),
      some r ∈ support (fsRunM queryH S fuel p cv h) → Prog.Returns p r.1
  | .ret a, cv, h, r, hr => by
    simp only [fsRunM, support_pure, Set.mem_singleton_iff, Option.some.injEq] at hr
    subst hr
    exact .ret a
  | .fail, cv, h, r, hr => by simp [fsRunM] at hr
  | .read k, cv, h, r, hr => by
    simp only [fsRunM, mem_support_bind_iff] at hr
    obtain ⟨cv', -, hr⟩ := hr
    exact .read _ (returns_of_mem_support_fsRunM S fuel _ _ _ r hr)
  | .sample k, cv, h, r, hr => by
    simp only [fsRunM, mem_support_bind_iff] at hr
    obtain ⟨cv', -, hr⟩ := hr
    exact .sample _ (returns_of_mem_support_fsRunM S fuel _ _ _ r hr)
  | .grind bits k, cv, h, r, hr => by
    simp only [fsRunM, mem_support_bind_iff] at hr
    obtain ⟨n?, -, hr⟩ := hr
    rcases n? with _ | n
    · simp at hr
    · simp only [mem_support_bind_iff] at hr
      obtain ⟨cv', -, hr⟩ := hr
      exact .grind bits (returns_of_mem_support_fsRunM S fuel _ _ _ r hr)
  | .commit ht w k, cv, h, r, hr => by
    simp only [fsRunM] at hr
    split at hr
    · simp only [mem_support_bind_iff] at hr
      obtain ⟨_, -, _, -, _, -, hr⟩ := hr
      exact .commit ht w (returns_of_mem_support_fsRunM S fuel _ _ _ r hr)
    · simp at hr
  | .query i ps k, cv, h, r, hr => by
    simp only [fsRunM] at hr
    split at hr
    · simp at hr
    · exact .query i ps _ (returns_of_mem_support_fsRunM S fuel _ _ _ r hr)

/-- **V°'s prefix returns claims of the bytecode's shapes.** -/
theorem freshShapedFor_of_returns_claimsProg {bc : List K} {pd : Digest} {c : FixedClaims}
    (h : Prog.Returns (claimsProg bc pd) c) : FreshShapedFor bc c := by
  unfold claimsProg at h
  obtain ⟨a, ha, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨t, ht, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨zc, hz, h⟩ := Prog.returns_bind h
  obtain ⟨u, hu, h⟩ := Prog.returns_bind h
  rw [Prog.returns_ret h]
  have hl := readSizes_logBytecode ha
  -- the bus phase's point
  unfold busPre at ht
  obtain ⟨alphas, hal, ht⟩ := Prog.returns_bind ht
  obtain ⟨_, -, ht⟩ := Prog.returns_bind ht
  obtain ⟨g, hg, ht⟩ := Prog.returns_bind ht
  obtain ⟨_, -, ht⟩ := Prog.returns_bind ht
  obtain ⟨_, -, ht⟩ := Prog.returns_bind ht
  obtain ⟨_, -, ht⟩ := Prog.returns_bind ht
  obtain ⟨_, -, ht⟩ := Prog.returns_bind ht
  rw [Prog.returns_ret ht]
  have hd := busLayout_depth_ge a.1.logMemory a.1.logBytecode a.1.push
  have hp := returns_verifyGkrGrandProducts hg
  have hs := Prog.returns_sampleN hal
  -- the lincheck's reads
  unfold linPre at hu
  obtain ⟨_, -, hu⟩ := Prog.returns_bind hu
  obtain ⟨x, hx, hu⟩ := Prog.returns_bind hu
  obtain ⟨s, hs', hu⟩ := Prog.returns_bind hu
  rw [Prog.returns_ret hu]
  have hchi := returns_verifyFlockZerocheck hz
  have hx' := returns_sumcheck hx
  have hr := Prog.returns_readN hs'
  have h7 : fixedChallenges.length = 7 := by simp [fixedChallenges]
  have h6 : flockKSkip = 6 := by decide
  have h8 : flockNumLincheckRounds = 8 := rfl
  have h14 : blake2sR1csLogSize = 14 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [freshOf, bcPoint, List.length_append, List.length_take]
    rw [hp, hs, ← hl]
    omega
  · simp only [freshOf, List.length_take]
    rw [hchi]
    omega
  · simp only [freshOf, List.length_reverse]
    rw [hx', List.length_replicate, h8]
  · simp only [freshOf]
    rw [hr]
    rfl

/-- **The fresh claims' run returns claims of the bytecode's shapes.** -/
theorem freshShapedFor_of_mem_support_freshRunM {S : Strategy} {fuel : ℕ} {bc : List K}
    {pd seed : Digest} {c : FixedClaims}
    (h : some c ∈ support (freshRunM queryH S fuel bc pd seed)) : FreshShapedFor bc c := by
  simp only [freshRunM, support_map, Set.mem_image] at h
  obtain ⟨r, hr, he⟩ := h
  rcases r with _ | r
  · cases he
  · cases he
    exact freshShapedFor_of_returns_claimsProg (returns_of_mem_support_fsRunM S fuel _ _ _ r hr)

theorem leafDefer_shaped : leafDefer.Shaped End.bytecode := by
  simp only [DeferredClaim.Shaped, leafDefer, List.length_replicate, and_self]

end FreshShape

/-! ## The shapes of the prover's outputs -/

section OutShape

variable (ρ pfuel : ℕ)

/-- **An output of the bytecode's shapes**: its fresh claims and its statement's deferred claim. -/
def OutShapedN (o : HonestOutN) : Prop :=
  FreshShapedFor End.bytecode o.fresh ∧ o.stmt.defer.Shaped End.bytecode

theorem childShaped_of_outShapedN {o : HonestOutN} (h : OutShapedN o) (pi : Digest) :
    ChildShaped End.bytecode ⟨pi, o.child.fresh, o.child.statement.defer⟩ := h

/-- The children's claims are the children's fresh and deferred claims, with some public inputs. -/
theorem fst_of_mem_support_claimsOfM :
    ∀ (cs : List Child) (ccs : List ChildClaims), ccs ∈ support (claimsOfM queryH cs) →
      ccs.map (fun c ↦ (c.fresh, c.carried)) = cs.map fun c ↦ (c.fresh, c.statement.defer)
  | [], ccs, h => by simp [claimsOfM] at h; simp [h]
  | c :: cs, ccs, h => by
    simp only [claimsOfM, List.mapM_cons, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at h
    obtain ⟨cc, ⟨pi, -, rfl⟩, rest, hrest, rfl⟩ := h
    simp only [List.map_cons, List.cons.injEq, true_and]
    exact fst_of_mem_support_claimsOfM cs rest hrest

/-- The honest hints' rounds: `Nat.log2` of the bytecode's length, and `zeroRounds`. -/
theorem rounds_of_mem_support_honestBatchM {s0 : Digest} {bytecode : List K}
    {cs : List ChildClaims} {wh : (E × E) × BatchHints}
    (h : wh ∈ support (honestBatchM queryH s0 bytecode cs)) :
    wh.2.bytecodeRounds.length = Nat.log2 bytecode.length ∧ wh.2.matrixRounds = zeroRounds := by
  unfold honestBatchM at h
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
  obtain ⟨_, -, _, -, rounds, hr, _, -, _, -, _, -, rfl⟩ := h
  exact ⟨length_of_mem_support_honestRoundsM _ _ _ _ _ rounds hr, rfl⟩

/-- **The deferred claim and hints of the honest batching**: of the bytecode's shapes, with the
honest rounds. -/
theorem honestDeferM_shape {cs : List Child} {hd : BatchHints × DeferredClaim}
    (h : Except.ok hd ∈ support (honestDeferM queryH cs).run) :
    hd.2.Shaped End.bytecode ∧
      hd.1.bytecodeRounds.length ≤ Nat.log2 End.bytecode.length ∧
      hd.1.matrixRounds.length ≤ 2 * blake2sR1csLogSize := by
  unfold honestDeferM at h
  split at h
  · rw [mem_support_exceptT_pure h]
    exact ⟨leafDefer_shaped, Nat.zero_le _, Nat.zero_le _⟩
  · obtain ⟨ccs, -, h⟩ := mem_support_exceptT_bind h
    obtain ⟨wh, hwh, h⟩ := mem_support_exceptT_bind h
    have hr := rounds_of_mem_support_honestBatchM (mem_support_exceptT_lift hwh)
    split at h
    · exact (not_mem_support_exceptT_throw h).elim
    · obtain ⟨r, -, h⟩ := mem_support_exceptT_bind h
      split at h
      · split at h
        · rw [mem_support_exceptT_pure h]
          rename_i d _ hb
          refine ⟨hb.1, hr.1.le, ?_⟩
          rw [hr.2]
          simp [zeroRounds]
        · exact (not_mem_support_exceptT_throw h).elim
      · exact (not_mem_support_exceptT_throw h).elim

/-- **A node's proof's output**: its statement, and fresh claims of the bytecode's shapes. -/
theorem proveNodeM_shape {s : NodeStatement} {w : NodeWitness} {kos : List HonestOutN}
    {o : HonestOutN} (h : Except.ok o ∈ support (proveNodeM queryH ρ pfuel s w kos).run) :
    o.stmt = s ∧ FreshShapedFor End.bytecode o.fresh := by
  unfold proveNodeM at h
  obtain ⟨pi, -, h⟩ := mem_support_exceptT_bind h
  obtain ⟨L, -, h⟩ := mem_support_exceptT_bind h
  split at h
  · exact (not_mem_support_exceptT_throw h).elim
  · obtain ⟨seed, -, h⟩ := mem_support_exceptT_bind h
    obtain ⟨r, -, h⟩ := mem_support_exceptT_bind h
    split at h
    · exact (not_mem_support_exceptT_throw h).elim
    · obtain ⟨c?, hc, h⟩ := mem_support_exceptT_bind h
      split at h
      · exact (not_mem_support_exceptT_throw h).elim
      · rename_i c
        obtain ⟨kids, -, h⟩ := mem_support_exceptT_bind h
        rw [mem_support_exceptT_pure h]
        exact ⟨rfl, freshShapedFor_of_mem_support_freshRunM (mem_support_exceptT_lift hc)⟩

/-- **The node step's output is of the bytecode's shapes.** -/
theorem honestStepM_shape {claims : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)}
    {kos : List HonestOutN} {o : HonestOutN}
    (h : Except.ok o ∈ support (honestStepM queryH ρ pfuel claims xs ss ds kos).run) :
    OutShapedN o := by
  unfold honestStepM at h
  obtain ⟨hd, hhd, h⟩ := mem_support_exceptT_bind h
  obtain ⟨hs, hf⟩ := proveNodeM_shape ρ pfuel h
  exact ⟨hf, hs ▸ (honestDeferM_shape hhd).1⟩

theorem honestProverM_node {c : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)}
    {kids : List HonestTree} :
    honestProverM queryH ρ pfuel (.node c xs ss ds kids) =
      (kids.attach.mapM fun k ↦ honestProverM queryH ρ pfuel k.1) >>=
        honestStepM queryH ρ pfuel c xs ss ds := by
  rw [honestProverM]

/-- **Every output of the prover is of the bytecode's shapes.** -/
theorem outShapedN_of_mem_support (T : HonestTree) {o : HonestOutN}
    (h : Except.ok o ∈ support (honestProverComp ρ pfuel T)) : OutShapedN o := by
  obtain ⟨c, xs, ss, ds, kids⟩ := T
  unfold honestProverComp at h
  rw [honestProverM_node] at h
  obtain ⟨kos, -, h⟩ := mem_support_exceptT_bind h
  exact honestStepM_shape ρ pfuel h

end OutShape

/-! ## The counts -/

section Counts

/-- The seed makes three queries. -/
theorem isTotalQueryBound_seedWith_queryH (bc : List K) (pd : Digest) :
    IsTotalQueryBound (seedWith queryH bc pd) 3 :=
  isTotalQueryBound_queryH_bind _ fun _ ↦ isTotalQueryBound_queryH_bind _ fun _ ↦
    isTotalQueryBound_queryH_one _

/-- **The batching's queries** at `n` shaped children (none at a leaf): the children's digests,
the honest hints, the batching. -/
def deferQueries (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    n * 7 + (1 + n * childLen 22 + 5 * n + 6 * 22 + 6 * blake2sR1csLogSize) +
      (1 + n * childLen 22 + 2 * n + 3 * 22 + 3 * n + 3 * (2 * blake2sR1csLogSize))

/-- **The node's checks' queries** at `n` shaped children with the honest rounds. -/
def checksQueries (n : ℕ) (c : Claims) (xs : List (Holder LeanXmss.Signature))
    (ss : List (Holder Sphincs.Signature)) (ds : List (Holder Da.Witness)) : ℕ :=
  5 + n * (6 + leanVmCost) +
    holdersQueries (fun _ _ ↦ xmssVerifyBound) c.xmss xs +
    holdersQueries (fun _ _ ↦ sphincsVerifyBound) c.sphincs ss +
    holdersQueries (fun (_ : DaClaim) (dw : Da.Witness) ↦ daQueries dw.rows.length) c.da ds +
    n * 5 + (1 + n * childLen 22 + 5 * n + 3 * 22 + 3 * (2 * blake2sR1csLogSize))

/-- **A node's own queries** at `n` children: the batching, the statement's digest, the logged
checks, the seed, V°'s proof, the fresh claims' run, the children's digests. -/
def nodeOwnQueries (pfuel n : ℕ) (c : Claims) (xs : List (Holder LeanXmss.Signature))
    (ss : List (Holder Sphincs.Signature)) (ds : List (Holder Da.Witness)) : ℕ :=
  deferQueries n + (7 + ((2 + checksQueries n c xs ss ds) +
    (3 + (leanVmCost * proverFactor costHeight pfuel +
      (leanVmCost * proverFactor costHeight pfuel + n * 7)))))

/-- **The honest prover's queries on a tree**: every node's own. -/
def HonestTree.proverQueries (ρ pfuel : ℕ) : HonestTree → ℕ
  | .node c xs ss ds kids =>
    (kids.attach.map fun k ↦ k.1.proverQueries ρ pfuel).sum +
      nodeOwnQueries pfuel kids.length c xs ss ds
termination_by T => sizeOf T
decreasing_by
  have := List.sizeOf_lt_of_mem k.2
  simp_wf
  omega

theorem HonestTree.proverQueries_node {ρ pfuel : ℕ} {c : Claims}
    {xs : List (Holder LeanXmss.Signature)} {ss : List (Holder Sphincs.Signature)}
    {ds : List (Holder Da.Witness)} {kids : List HonestTree} :
    (HonestTree.node c xs ss ds kids).proverQueries ρ pfuel =
      (kids.attach.map fun k ↦ k.1.proverQueries ρ pfuel).sum +
        nodeOwnQueries pfuel kids.length c xs ss ds := by
  rw [HonestTree.proverQueries]

variable (ρ pfuel : ℕ)

/-- Shaped children's cells: `childLen` each. -/
theorem sum_cells_le {kos : List HonestOutN} (hk : ∀ ko ∈ kos, OutShapedN ko) :
    ((kos.map HonestOutN.child).map fun c ↦
      2 + (fixedCells c.fresh ++ c.statement.defer.cells).length).sum ≤
        kos.length * childLen 22 := by
  rw [List.map_map]
  refine (sum_map_le_mul _ (childLen 22) kos fun ko hko ↦ ?_)
  have := length_childCells (childShaped_of_outShapedN (hk ko hko) 0)
  rw [log2_bytecode_length_eq] at this
  simp only [childCells, List.length_append, List.length_cons, List.length_nil] at this
  simp only [Function.comp_apply, List.length_append]
  omega

/-- **The node's checks' queries** at shaped children and the honest rounds. -/
theorem nodeChecksQueries_le_checksQueries {claims : Claims} {d : DeferredClaim}
    {xs : List (Holder LeanXmss.Signature)} {ss : List (Holder Sphincs.Signature)}
    {ds : List (Holder Da.Witness)} {kos : List HonestOutN} {h : BatchHints}
    (hk : ∀ ko ∈ kos, OutShapedN ko)
    (hb : h.bytecodeRounds.length ≤ Nat.log2 End.bytecode.length)
    (hm : h.matrixRounds.length ≤ 2 * blake2sR1csLogSize) :
    nodeChecksQueries ⟨claims, d⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, h⟩ ≤
      checksQueries kos.length claims xs ss ds := by
  have hs := sum_cells_le hk
  rw [log2_bytecode_length_eq] at hb
  unfold nodeChecksQueries checksQueries
  simp only [List.length_map] at hs ⊢
  omega

/-- The children's claims' cells, at shaped children. -/
theorem flatMap_childCells_length {kos : List HonestOutN} (hk : ∀ ko ∈ kos, OutShapedN ko)
    {ccs : List ChildClaims} (h : ccs ∈ support (claimsOfM queryH (kos.map HonestOutN.child))) :
    ccs.length = kos.length ∧ (ccs.flatMap childCells).length ≤ kos.length * childLen 22 ∧
      (ccs.map fun c ↦ 2 + (fixedCells c.fresh ++ c.carried.cells).length).sum ≤
        kos.length * childLen 22 := by
  have hm := fst_of_mem_support_claimsOfM _ ccs h
  have hlen : ccs.length = kos.length := by simpa using congrArg List.length hm
  have hsh : ∀ cc ∈ ccs, ChildShaped End.bytecode cc := by
    intro cc hcc
    have : (cc.fresh, cc.carried) ∈ (kos.map HonestOutN.child).map
        fun c ↦ (c.fresh, c.statement.defer) := hm ▸ List.mem_map_of_mem hcc
    simp only [List.map_map, List.mem_map, Function.comp_apply] at this
    obtain ⟨ko, hko, he⟩ := this
    simp only [HonestOutN.child, Prod.mk.injEq] at he
    exact ⟨he.1 ▸ (hk ko hko).1, he.2 ▸ (hk ko hko).2⟩
  have hcl : ∀ cc ∈ ccs, (childCells cc).length = childLen 22 := fun cc hcc ↦ by
    rw [length_childCells (hsh cc hcc), log2_bytecode_length_eq]
  refine ⟨hlen, ?_, ?_⟩
  · rw [List.length_flatMap, ← hlen]
    exact sum_map_le_mul _ _ ccs fun cc hcc ↦ (hcl cc hcc).le
  · rw [← hlen]
    refine sum_map_le_mul _ _ ccs fun cc hcc ↦ ?_
    have := hcl cc hcc
    simp only [childCells, List.length_append, List.length_cons, List.length_nil] at this ⊢
    omega

/-- **The batching's queries** at shaped children. -/
theorem isTotalQueryBound_honestDeferM {kos : List HonestOutN}
    (hk : ∀ ko ∈ kos, OutShapedN ko) :
    IsTotalQueryBound (honestDeferM queryH (kos.map HonestOutN.child)).run
      (deferQueries kos.length) := by
  unfold honestDeferM
  split
  · exact isTotalQueryBound_exceptT_pure _ _
  · rename_i hne
    have hn : kos.length ≠ 0 := by
      intro h0
      exact hne (by simp [List.length_eq_zero_iff.mp h0])
    refine (isTotalQueryBound_exceptT_bind (isTotalQueryBound_exceptT_lift
      (isTotalQueryBound_mapM _ 7 (fun _ ↦ isTotalQueryBound_bind (n₂ := 0)
        (isTotalQueryBound_digestOfM _) fun _ ↦ isTotalQueryBound_pure' _ 0) _))
      (n₂ := (1 + kos.length * childLen 22 + 5 * kos.length + 6 * 22 +
        6 * blake2sR1csLogSize) + ((1 + kos.length * childLen 22 + 2 * kos.length + 3 * 22 +
        3 * kos.length + 3 * (2 * blake2sR1csLogSize)) + 0))
      fun ccs hccs ↦ ?_).mono ?_
    · obtain ⟨hlen, hcells, hsum⟩ :=
        flatMap_childCells_length hk (mem_support_exceptT_lift hccs)
      refine isTotalQueryBound_exceptT_bind (isTotalQueryBound_exceptT_lift
        ((isTotalQueryBound_honestBatchM _ _ ccs).mono ?_)) fun wh hwh ↦ ?_
      · simp only [honestBatchQueries, log2_bytecode_length_eq, hlen]
        omega
      · have hr := rounds_of_mem_support_honestBatchM (mem_support_exceptT_lift hwh)
        split
        · exact isTotalQueryBound_exceptT_throw _ _
        · refine isTotalQueryBound_exceptT_bind (isTotalQueryBound_exceptT_lift
            ((isTotalQueryBound_batchWith _ ccs wh.2).mono ?_)) fun r _ ↦ ?_
          · simp only [batchQueries, hr.1, hr.2, log2_bytecode_length_eq, hlen, zeroRounds,
              List.length_replicate]
            omega
          · split
            · split
              · exact isTotalQueryBound_exceptT_pure _ _
              · exact isTotalQueryBound_exceptT_throw _ _
            · exact isTotalQueryBound_exceptT_throw _ _
    · simp only [deferQueries, hn, ↓reduceIte, List.length_map]
      omega

/-- **A node's proof's queries** at shaped children and the honest rounds. -/
theorem isTotalQueryBound_proveNodeM {claims : Claims} {d : DeferredClaim}
    {xs : List (Holder LeanXmss.Signature)} {ss : List (Holder Sphincs.Signature)}
    {ds : List (Holder Da.Witness)} {kos : List HonestOutN} {h : BatchHints}
    (hk : ∀ ko ∈ kos, OutShapedN ko)
    (hb : h.bytecodeRounds.length ≤ Nat.log2 End.bytecode.length)
    (hm : h.matrixRounds.length ≤ 2 * blake2sR1csLogSize) :
    IsTotalQueryBound
      (proveNodeM queryH ρ pfuel ⟨claims, d⟩ ⟨kos.map HonestOutN.child, xs, ss, ds, h⟩ kos).run
      (7 + ((2 + checksQueries kos.length claims xs ss ds) +
        (3 + (leanVmCost * proverFactor costHeight pfuel +
          (leanVmCost * proverFactor costHeight pfuel + kos.length * 7))))) := by
  have hc := nodeChecksQueries_le_checksQueries (claims := claims) (d := d) (xs := xs) (ss := ss)
    (ds := ds) hk hb hm
  unfold proveNodeM
  refine isTotalQueryBound_exceptT_bind (isTotalQueryBound_exceptT_lift
    (isTotalQueryBound_digestOfM _)) fun pi _ ↦ isTotalQueryBound_exceptT_bind
    (isTotalQueryBound_exceptT_lift ((isTotalQueryBound_nodeLogPairsM _ _).mono
      (Nat.add_le_add_left hc 2))) fun L _ ↦ ?_
  split
  · exact isTotalQueryBound_exceptT_throw _ _
  · refine isTotalQueryBound_exceptT_bind (isTotalQueryBound_exceptT_lift
      (isTotalQueryBound_seedWith_queryH _ _)) fun seed _ ↦ isTotalQueryBound_exceptT_bind
      (isTotalQueryBound_exceptT_lift (isTotalQueryBound_proveM
        (costLE_blindProgram _ _) _ _ _)) fun r _ ↦ ?_
    split
    · exact isTotalQueryBound_exceptT_throw _ _
    · refine isTotalQueryBound_exceptT_bind (isTotalQueryBound_exceptT_lift
        (isTotalQueryBound_freshRunM _ _ _ _ _)) fun c? _ ↦ ?_
      split
      · exact isTotalQueryBound_exceptT_throw _ _
      · rw [← Nat.add_zero (kos.length * 7)]
        exact isTotalQueryBound_exceptT_bind (isTotalQueryBound_exceptT_lift
          (isTotalQueryBound_mapM _ 7 (fun _ ↦ isTotalQueryBound_bind (n₂ := 0)
            (isTotalQueryBound_digestOfM _) fun _ ↦ isTotalQueryBound_pure' _ 0) _))
          fun _ _ ↦ isTotalQueryBound_exceptT_pure _ _

/-- **The node step's queries** at shaped children. -/
theorem isTotalQueryBound_honestStepM (claims : Claims) (xs : List (Holder LeanXmss.Signature))
    (ss : List (Holder Sphincs.Signature)) (ds : List (Holder Da.Witness))
    {kos : List HonestOutN} (hk : ∀ ko ∈ kos, OutShapedN ko) :
    IsTotalQueryBound (honestStepM queryH ρ pfuel claims xs ss ds kos).run
      (nodeOwnQueries pfuel kos.length claims xs ss ds) := by
  unfold honestStepM nodeOwnQueries
  refine isTotalQueryBound_exceptT_bind (isTotalQueryBound_honestDeferM hk) fun hd hhd ↦ ?_
  obtain ⟨-, hb, hm⟩ := honestDeferM_shape hhd
  exact isTotalQueryBound_proveNodeM ρ pfuel hk hb hm

/-- **The honest prover's queries**: at most `T.proverQueries ρ pfuel`, a function of the tree. -/
theorem isTotalQueryBound_honestProverComp :
    ∀ T : HonestTree, IsTotalQueryBound (honestProverComp ρ pfuel T) (T.proverQueries ρ pfuel)
  | .node c xs ss ds kids => by
    unfold honestProverComp
    rw [honestProverM_node, HonestTree.proverQueries_node]
    refine isTotalQueryBound_exceptT_bind (isTotalQueryBound_exceptT_mapM _
      (fun k ↦ k.1.proverQueries ρ pfuel) kids.attach fun k _ ↦
        isTotalQueryBound_honestProverComp k.1) fun kos hkos ↦ ?_
    have hF := forall₂_of_mem_support_exceptT_mapM _ _ _ hkos
    have hlen : kos.length = kids.length := by
      rw [← hF.length_eq, List.length_attach]
    have hk : ∀ ko ∈ kos, OutShapedN ko := fun ko hko ↦ by
      obtain ⟨k, -, hk⟩ := E2E.exists_of_forall₂_right hF ko hko
      exact outShapedN_of_mem_support ρ pfuel k.1 hk
    rw [← hlen]
    exact isTotalQueryBound_honestStepM ρ pfuel c xs ss ds hk
termination_by T => sizeOf T
decreasing_by
  have := List.sizeOf_lt_of_mem k.2
  simp_wf
  omega

end Counts

/-! ## The closed bound -/

section Closed

/-- **The shape a node's closed bound needs**: at most sixteen children, `2^16` signature claims,
at most one DA opening held directly, of at most `LeanDa.maxRows` rows. -/
def HonestTree.ShapeOK : HonestTree → Prop
  | .node c _ _ ds kids =>
    kids.length ≤ 16 ∧ c.xmss.length + c.sphincs.length ≤ 2 ^ 16 ∧
      (Hints.direct c.da ds).length ≤ 1 ∧
      ∀ dw, Holder.direct dw ∈ ds → dw.rows.length ≤ LeanDa.maxRows

theorem HonestTree.ShapeOK.kidsLe16 {T : HonestTree} (h : HonestTree.ShapeOK T) :
    HonestTree.KidsLe16 T := by
  obtain ⟨c, xs, ss, ds, kids⟩ := T
  exact h.1

/-- The node's checks' closed bound (`nodeChecksBound`'s, at the honest rounds). -/
def checksBound : ℕ :=
  5 + 16 * (6 + leanVmCost) + sphincsVerifyBound * 2 ^ 16 + 329730 + 16 * 5 +
    (1 + 16 * childLen 22 + 5 * 16 + 3 * 22 + 3 * (2 * blake2sR1csLogSize))

/-- **A node's queries, closed**: the batching of sixteen children, the checks, V°'s proof and the
fresh claims' run (`leanVmCost · proverFactor costHeight pfuel` each), the digests. -/
def nodeQueries (pfuel : ℕ) : ℕ :=
  deferQueries 16 + (7 + ((2 + checksBound) +
    (3 + (leanVmCost * proverFactor costHeight pfuel +
      (leanVmCost * proverFactor costHeight pfuel + 16 * 7)))))

/-- **A node's queries' value**: `45,507,690` beside V°'s proof and the fresh claims' run,
`26,420 · (2^27 + pfuel + 1)`; about `2^42` at `pfuel = 2^25`. -/
theorem nodeQueries_eq (pfuel : ℕ) :
    nodeQueries pfuel = 45507690 + 26420 * (2 ^ 27 + pfuel + 1) := by
  have h1 : deferQueries 16 = 5792 := by decide
  have h2 : checksBound = 45501774 := by decide
  have h3 : leanVmCost = 13210 := by decide
  have h4 : proverFactor costHeight pfuel = 2 ^ 27 + pfuel + 1 := rfl
  unfold nodeQueries
  rw [h1, h2, h3, h4]
  omega

theorem deferQueries_le {n : ℕ} (hn : n ≤ 16) : deferQueries n ≤ deferQueries 16 := by
  have h1 : n * childLen 22 ≤ 16 * childLen 22 := Nat.mul_le_mul_right _ hn
  unfold deferQueries
  split
  · exact Nat.zero_le _
  · simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
    omega

theorem checksQueries_le {c : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)} {kids : List HonestTree}
    (h : HonestTree.ShapeOK (.node c xs ss ds kids)) :
    checksQueries kids.length c xs ss ds ≤ checksBound := by
  obtain ⟨hch, hcv, hdir, hda⟩ := h
  have hx := holdersQueries_le (fun (_ : XmssClaim) (_ : LeanXmss.Signature) ↦ xmssVerifyBound)
    sphincsVerifyBound c.xmss xs fun _ _ _ ↦ by decide
  have hs := holdersQueries_le (fun (_ : SphincsClaim) (_ : Sphincs.Signature) ↦
    sphincsVerifyBound) sphincsVerifyBound c.sphincs ss fun _ _ _ ↦ le_rfl
  have hd := holdersQueries_le (fun (_ : DaClaim) (dw : Da.Witness) ↦ daQueries dw.rows.length)
    329730 c.da ds fun dw hdw _ ↦ daQueries_le (hda dw hdw)
  have hlx := length_direct_le c.xmss xs
  have hls := length_direct_le c.sphincs ss
  have hxy : (Hints.direct c.xmss xs).length * sphincsVerifyBound +
      (Hints.direct c.sphincs ss).length * sphincsVerifyBound ≤ sphincsVerifyBound * 2 ^ 16 := by
    rw [← Nat.add_mul, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  have h1 : kids.length * (6 + leanVmCost) ≤ 16 * (6 + leanVmCost) := Nat.mul_le_mul_right _ hch
  have h2 : kids.length * childLen 22 ≤ 16 * childLen 22 := Nat.mul_le_mul_right _ hch
  have hdd : (Hints.direct c.da ds).length * 329730 ≤ 329730 := by
    have := Nat.mul_le_mul_right 329730 hdir
    omega
  unfold checksQueries checksBound
  omega

/-- **A node's own queries, closed.** -/
theorem nodeOwnQueries_le (pfuel : ℕ) {c : Claims} {xs : List (Holder LeanXmss.Signature)}
    {ss : List (Holder Sphincs.Signature)} {ds : List (Holder Da.Witness)} {kids : List HonestTree}
    (h : HonestTree.ShapeOK (.node c xs ss ds kids)) :
    nodeOwnQueries pfuel kids.length c xs ss ds ≤ nodeQueries pfuel := by
  have h1 := deferQueries_le h.1
  have h2 := checksQueries_le h
  have h3 : kids.length * 7 ≤ 16 * 7 := Nat.mul_le_mul_right _ h.1
  unfold nodeOwnQueries nodeQueries
  omega

theorem sum_map_le_sum_map_mul {α : Type} (f g : α → ℕ) (K : ℕ) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ g a * K) → (l.map f).sum ≤ (l.map g).sum * K
  | [], _ => by simp
  | a :: l, h => by
    have ih := sum_map_le_sum_map_mul f g K l fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    have := h a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    omega

/-- **The prover's queries, closed**: at most `nodeQueries pfuel` per node, under `ShapeOK`. -/
theorem proverQueries_le (ρ pfuel : ℕ) :
    ∀ T : HonestTree, T.AllNodes HonestTree.ShapeOK →
      T.proverQueries ρ pfuel ≤ T.size * nodeQueries pfuel
  | .node c xs ss ds kids, hs => by
    rw [HonestTree.allNodes_node] at hs
    rw [HonestTree.proverQueries_node, HonestTree.size]
    have ih := sum_map_le_sum_map_mul (fun k : {x // x ∈ kids} ↦ k.1.proverQueries ρ pfuel)
      (fun k ↦ k.1.size) (nodeQueries pfuel) kids.attach fun k _ ↦
        proverQueries_le ρ pfuel k.1 (hs.2 k.1 k.2)
    have hown := nodeOwnQueries_le pfuel hs.1
    rw [Nat.add_mul, one_mul]
    omega
termination_by T => sizeOf T
decreasing_by
  have := List.sizeOf_lt_of_mem k.2
  simp_wf
  omega

end Closed

end
end LeanVM.E2E.Complete
