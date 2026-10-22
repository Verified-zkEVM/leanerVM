/-
  LeanVM.E2E.BudgetCount

  V_I's query count, piece by piece: the counted monad's laws, the counts of V_I's hashing pieces
  (the IV, a statement's digest, V°, the outer checks, a partial tree's root, the table check),
  and the closure's count from a bound per node.
-/

module

public import LeanVM.E2E.Budget
public import LeanVM.Protocol.EndToEnd.Blind.Cost

/-!
# V_I's query count, piece by piece

`Budget.lean` defines V_I's query count `queryCount H prog ip fuel s`: the hash queries of V_I's
run with `H`, in the counted monad (`Counted`: a value and a count, the counts of a sequence
added). This file bounds it from bounds on its pieces:

* the IV `2` (`count_fiatShamirIvWith`) and a statement's digest `5`
  (`count_statementDigestWith`);
* V° at most `leanVmQueryBound = 13,213` on every proof (`count_verifyBlindWith_le`), from its
  query bound in the random-oracle model (`isTotalQueryBound_blind`) through
  `count_simulateQ_le`: a computation making at most `n` queries counts at most `n`, whatever
  the hash;
* the outer checks `18` per DA claim (`count_outerChecksWith_le`);
* a partial tree of height `ht`, at most `2^(ht+1) − 1` (`count_pTreeRootM_le`), and the stack's
  tree in V_I has height at most `costHeight = 26` (`stackShape_height_le`, from the ladders'
  bound `ladder_cost`), so at most `2^27 − 1`;
* the table check at most the number of strings with a standard chain among the rows
  (`count_tableOKWith_le`);
* the closure at most `fuel · C` when every node it reaches costs at most `C`
  (`count_closure_le`).

So **`queryCount_le_of`**: V_I's count is at most `2 + 5 + 13,213 + 18 · |da| + fuel · C` when
the nodes good for `C` (each step at most `C` queries, its children good) contain the root.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom
open OracleSpec OracleComp

@[expose] public section

/-! ## The counted monad's laws -/

namespace Counted

variable {α β : Type}

@[simp] theorem count_pure (a : α) : (pure a : Counted α).count = 0 := rfl

@[simp] theorem val_pure (a : α) : (pure a : Counted α).val = a := rfl

@[simp] theorem count_bind (x : Counted α) (f : α → Counted β) :
    (x >>= f).count = x.count + (f x.val).count := rfl

@[simp] theorem val_bind (x : Counted α) (f : α → Counted β) : (x >>= f).val = (f x.val).val :=
  rfl

@[simp] theorem count_map (f : α → β) (x : Counted α) : (f <$> x).count = x.count := by
  rw [map_eq_bind_pure_comp, count_bind]
  rfl

@[simp] theorem val_map (f : α → β) (x : Counted α) : (f <$> x).val = f x.val := by
  rw [map_eq_bind_pure_comp, val_bind]
  rfl

end Counted

@[simp] theorem count_countQuery (H : Bytes → Digest) (x : Bytes) : (countQuery H x).count = 1 :=
  rfl

@[simp] theorem val_countQuery (H : Bytes → Digest) (x : Bytes) : (countQuery H x).val = H x :=
  rfl

/-- A `for` loop over a list costs at most its bodies' bounds. -/
theorem count_forIn_le {γ β : Type} (f : γ → β → Counted (ForInStep β)) (c : γ → ℕ)
    (hf : ∀ a b, (f a b).count ≤ c a) :
    ∀ (l : List γ) (b : β), (forIn l b f).count ≤ (l.map c).sum
  | [], _ => by simp
  | a :: l, b => by
    rw [List.forIn_cons, Counted.count_bind, List.map_cons, List.sum_cons]
    refine Nat.add_le_add (hf a b) ?_
    cases (f a b).val with
    | done => simp
    | yield b' => exact count_forIn_le f c hf l b'

/-- A `foldlM` costs at most its bodies' bounds. -/
theorem count_foldlM_le {γ β : Type} (f : β → γ → Counted β) (c : ℕ)
    (hf : ∀ b a, (f b a).count ≤ c) : ∀ (l : List γ) (b : β), (l.foldlM f b).count ≤ l.length * c
  | [], _ => by simp
  | a :: l, b => by
    rw [List.foldlM_cons, Counted.count_bind, List.length_cons, Nat.succ_mul]
    have := count_foldlM_le f c hf l (f b a).val
    have := hf b a
    omega

/-- An `allM` costs at most its bodies' bounds. -/
theorem count_allM_le {γ : Type} (f : γ → Counted Bool) (c : ℕ) (hf : ∀ a, (f a).count ≤ c) :
    ∀ l : List γ, (l.allM f).count ≤ l.length * c
  | [] => by simp
  | a :: l => by
    rw [List.allM_cons, Counted.count_bind, List.length_cons, Nat.succ_mul]
    have ih := count_allM_le f c hf l
    have ha := hf a
    rcases (f a).val with _ | _ <;> simp <;> omega

/-! ## From the random-oracle model's query bounds -/

/-- **A computation making at most `n` queries counts at most `n`**, whatever the hash. -/
theorem count_simulateQ_le (H : Bytes → Digest) {α : Type} (oa : OracleComp HashSpec α) :
    ∀ {n : ℕ}, IsTotalQueryBound oa n →
      (simulateQ (fun x ↦ countQuery H x : QueryImpl HashSpec Counted) oa).count ≤ n := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro n _; simp
  | query_bind t mx ih =>
    intro n h
    obtain ⟨hn, hk⟩ := isTotalQueryBound_query_bind_iff.mp h
    rw [simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id]
    change (countQuery H t >>= fun u ↦ simulateQ _ (mx u)).count ≤ n
    rw [Counted.count_bind, count_countQuery]
    have := ih (H t) (hk (H t))
    simp only [val_countQuery]
    omega

/-- Simulating every query by its count is a monad morphism. -/
theorem simulateQ_countQuery_rel_bind (H : Bytes → Digest) {α β : Type}
    (x : OracleComp HashSpec α) (y : Counted α) (f : α → OracleComp HashSpec β)
    (g : α → Counted β)
    (hx : simulateQ (fun x ↦ countQuery H x : QueryImpl HashSpec Counted) x = y)
    (hf : ∀ a, simulateQ (fun x ↦ countQuery H x : QueryImpl HashSpec Counted) (f a) = g a) :
    simulateQ (fun x ↦ countQuery H x : QueryImpl HashSpec Counted) (x >>= f) = y >>= g := by
  rw [simulateQ_bind, hx]
  exact congrArg _ (funext hf)

/-! ## The pieces -/

/-- The IV makes two queries. -/
theorem count_fiatShamirIvWith (H : Bytes → Digest) (bytecode : List K) :
    (fiatShamirIvWith (countQuery H) bytecode).count = 2 := rfl

/-- A statement's digest makes five queries. -/
theorem count_statementDigestWith (H : Bytes → Digest) (seed : Digest) (s : NodeStatement) :
    (statementDigestWith (countQuery H) seed s).count = 5 := rfl

/-- **V° makes at most `leanVmQueryBound = 13,213` queries** on every proof. -/
theorem count_verifyBlindWith_le (H : Bytes → Digest) (bytecode : List K) (pd : Digest)
    (π : Proof) : (verifyBlindWith (countQuery H) bytecode pd π).count ≤ leanVmQueryBound := by
  have h := count_simulateQ_le H _ (isTotalQueryBound_blind bytecode pd π)
  rw [simulateQ_verify] at h
  simpa only [Rom.verify, verifyBlindWith, seedRun_leanVmSeed] using h

/-- A DA hash makes one query. -/
@[simp] theorem count_daHash (H : Bytes → Digest) (x : List UInt8) :
    (Da.daHash (countQuery H) x).count = 1 := by
  unfold Da.daHash
  simp

/-- The DA squeezes make one query each. -/
theorem count_squeezesWith (H : Bytes → Digest) :
    ∀ (n : ℕ) (state : LeanDa.Digest),
      (Da.squeezesWith (Da.daHash (countQuery H)) n state).count = n
  | 0, _ => rfl
  | n + 1, state => by
    rw [Da.squeezesWith, Counted.count_bind, Counted.count_bind, Counted.count_pure,
      count_squeezesWith H n]
    unfold Da.compressWordsWith
    rw [count_daHash]
    omega

/-- A DA root's vector digest makes eighteen queries. -/
theorem count_vectorDigestOfWith (H : Bytes → Digest) (root : Digest) :
    (Da.vectorDigestOfWith (countQuery H) root).count = 18 := by
  unfold Da.vectorDigestOfWith Da.membershipVectorWith Da.membershipChallengesWith
    Da.vectorDigestWith Da.compressWordsWith
  simp only [Counted.count_bind, Counted.count_map, count_daHash, count_squeezesWith]
  rfl

/-- **The outer checks make eighteen queries per DA claim**, at most. -/
theorem count_outerChecksWith_le (H : Bytes → Digest) (prog : Program) (s : NodeStatement) :
    (outerChecksWith (countQuery H) prog s).count ≤ s.claims.da.length * 18 := by
  unfold outerChecksWith
  rw [Counted.count_bind, Counted.count_pure, Nat.add_zero]
  refine count_allM_le _ 18 (fun c ↦ ?_) _
  rw [Counted.count_bind, Counted.count_pure, Nat.add_zero, count_vectorDigestOfWith]

/-- **A partial tree's root makes at most `2^(k+1) − 1` queries** at height `k`, a hole none. -/
theorem count_pNodeM_le (H : Bytes → Digest) (P : PWord) :
    ∀ k j, (pNodeM (countQuery H) P k j).count + 1 ≤ 2 ^ (k + 1)
  | 0, j => by
    unfold pNodeM
    split <;> simp
  | k + 1, j => by
    unfold pNodeM
    split
    · simp only [Counted.count_pure]
      have := Nat.one_le_two_pow (n := k + 2)
      omega
    · simp only [Counted.count_bind, count_countQuery]
      have h1 := count_pNodeM_le H P k (2 * j)
      have h2 := count_pNodeM_le H P k (2 * j + 1)
      rw [Nat.pow_succ 2 (k + 1)]
      omega

/-- A partial tree's root at height `ht` makes at most `2^(ht+1) − 1` queries. -/
theorem count_pTreeRootM_le (H : Bytes → Digest) (ht : ℕ) (P : PWord) :
    (pTreeRootM (countQuery H) ht P).count + 1 ≤ 2 ^ (ht + 1) :=
  count_pNodeM_le H P ht 0

/-- **The stack's tree in V_I has height at most `costHeight`**: its shape is the first level of
an admissible ladder's (`ladder_cost`). -/
theorem stackShape_height_le {layout : Verifier.Layout} {ρ ht w : ℕ}
    (h : stackShape layout ρ = some (ht, w)) : ht ≤ costHeight := by
  unfold stackShape at h
  split at h
  · rename_i level rest hc
    have hl := (ladder_cost _ _ _ hc).2.1
    simp only [stackHeightLE, decide_eq_true_eq] at hl
    simp only [levelShape, Option.some.injEq, Prod.mk.injEq] at h
    omega
  · cases h

/-- **The table check makes at most one query per string with a standard chain among the
rows**, so at most the size of any set containing them. -/
theorem count_tableOKWith_le (H : Bytes → Digest) (rows : List BlakeRow) (D : Finset Bytes)
    (hD : chainInputs rows ⊆ ↑D) : (tableOKWith (countQuery H) rows).count ≤ D.card := by
  classical
  unfold tableOKWith
  split
  · split
    · rename_i hfin
      refine (count_allM_le _ 1 (fun x ↦ ?_) _).trans ?_
      · simp
      · rw [Nat.mul_one, Finset.length_toList]
        exact Finset.card_le_card fun x hx ↦ hD ((Set.Finite.mem_toFinset hfin).mp hx)
    · simp
  · simp

/-! ## The closure -/

/-- The value of a counted run is the `Id` run, as a relation. -/
def ValRel {α : Type} (x : Counted α) (y : Id α) : Prop := x.val = y

theorem valRel_pure {α : Type} (a : α) : ValRel (pure a : Counted α) (pure a) := rfl

theorem valRel_bind {α β : Type} (x : Counted α) (y : Id α) (f : α → Counted β) (g : α → Id β)
    (hx : ValRel x y) (hf : ∀ a, ValRel (f a) (g a)) : ValRel (x >>= f) (y >>= g) := by
  unfold ValRel at *
  rw [Counted.val_bind, hx]
  exact hf _

/-- **The value of a counted node step is the `Id` step.** -/
theorem val_nodeStep (H : Bytes → Digest) (prog : Program) (seed : Digest) (ip : IdealProof)
    (ν : Node) :
    (nodeStep (countQuery H) prog seed ip ν).val =
      nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) prog seed ip ν :=
  rel_nodeStep (fun {α : Type} (x : Counted α) (y : Id α) ↦ ValRel x y) valRel_pure valRel_bind
    (countQuery H) _ (fun _ ↦ rfl) prog seed ip ν

/-- **The closure's count**: every node it reaches good, a good node's step costs at most `C`
and steps to good children; then the closure costs at most `fuel · C`. -/
theorem count_closure_le (H : Bytes → Digest) (prog : Program) (seed : Digest) (ip : IdealProof)
    (Good : Node → Prop) (C : ℕ)
    (hcost : ∀ ν, Good ν → (nodeStep (countQuery H) prog seed ip ν).count ≤ C)
    (hkids : ∀ ν, Good ν → ∀ ks,
      nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) prog seed ip ν = some ks →
        ∀ κ ∈ ks, Good κ) :
    ∀ (fuel : ℕ) (todo done : List Node), (∀ ν ∈ todo, Good ν) →
      (closure (countQuery H) prog seed ip fuel todo done).count ≤ fuel * C
  | _, [], _, _ => by unfold closure; simp
  | 0, _ :: _, _, _ => by unfold closure; simp
  | fuel + 1, ν :: todo, done, hg => by
    have hν := hg ν List.mem_cons_self
    have hrest : ∀ κ ∈ todo, Good κ := fun κ hκ ↦ hg κ (List.mem_cons_of_mem ν hκ)
    unfold closure
    rw [Nat.succ_mul]
    split
    · exact (count_closure_le H prog seed ip Good C hcost hkids fuel todo done hrest).trans
        (Nat.le_add_right _ _)
    · rw [Counted.count_bind]
      have h1 := hcost ν hν
      have hv := val_nodeStep H prog seed ip ν
      generalize (nodeStep (countQuery H) prog seed ip ν) = x at h1 hv
      rcases hx : x.val with _ | ks
      · simp only [Counted.count_pure]
        omega
      · have hk := hkids ν hν ks (hv ▸ hx)
        have := count_closure_le H prog seed ip Good C hcost hkids fuel (todo ++ ks) (ν :: done)
          fun κ hκ ↦ by
            rcases List.mem_append.mp hκ with hκ | hκ
            · exact hrest κ hκ
            · exact hk κ hκ
        simp only
        omega

/-- **V_I's query count, from a bound per node**: the IV, the root's digest, V°, the outer
checks, and at most `fuel` node steps of at most `C` queries each, when the nodes good for `C`
contain the root. -/
theorem queryCount_le_of (H : Bytes → Digest) (prog : Program) (ip : IdealProof) (fuel : ℕ)
    (s : NodeStatement) (Good : Node → Prop) (C : ℕ)
    (hcost : ∀ ν, Good ν → (nodeStep (countQuery H) prog
      (Id.run (fiatShamirIvWith (fun x ↦ (pure (H x) : Id Digest)) (bytecodeWords prog))) ip
        ν).count ≤ C)
    (hkids : ∀ ν, Good ν → ∀ ks, nodeStep (m := Id) (fun x ↦ (pure (H x) : Id Digest)) prog
      (Id.run (fiatShamirIvWith (fun x ↦ (pure (H x) : Id Digest)) (bytecodeWords prog))) ip ν =
        some ks → ∀ κ ∈ ks, Good κ)
    (hroot : Good (Id.run (statementDigestWith (fun x ↦ (pure (H x) : Id Digest))
      (Id.run (fiatShamirIvWith (fun x ↦ (pure (H x) : Id Digest)) (bytecodeWords prog))) s),
        ip.proof)) :
    queryCount H prog ip fuel s ≤
      2 + 5 + leanVmQueryBound + s.claims.da.length * 18 + fuel * C := by
  unfold queryCount idealVerify
  simp only [Counted.count_bind, count_fiatShamirIvWith, count_statementDigestWith]
  have hV := count_verifyBlindWith_le H (bytecodeWords prog)
    (statementDigestWith (countQuery H) (fiatShamirIvWith (countQuery H) (bytecodeWords prog)).val
      s).val ip.proof
  have hO := count_outerChecksWith_le H prog s
  have hC := count_closure_le H prog
    (fiatShamirIvWith (countQuery H) (bytecodeWords prog)).val ip Good C hcost hkids fuel
    [((statementDigestWith (countQuery H)
      (fiatShamirIvWith (countQuery H) (bytecodeWords prog)).val s).val, ip.proof)] []
    (fun ν hν ↦ by rw [List.mem_singleton.mp hν]; exact hroot)
  generalize (verifyBlindWith (countQuery H) (bytecodeWords prog) _ ip.proof) = v at hV ⊢
  generalize (outerChecksWith (countQuery H) prog s) = oc at hO ⊢
  generalize (closure (countQuery H) prog _ ip fuel _ []) = cl at hC ⊢
  rcases hv' : v.val with _ | _ <;> rcases ho' : oc.val with _ | _ <;>
    simp [ho'] <;> omega

end
end LeanVM.E2E
