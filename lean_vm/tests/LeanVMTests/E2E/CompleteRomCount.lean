import LeanVM.E2E.Complete.Rom.Valid

/-!
# T6-prob's prover queries and valid generator, locked

Statement locks of `LeanVM/E2E/Complete/Rom/CompCount.lean` and `Rom/Valid.lean`
(`docs/roadmap/t6-prob.md` §4.4–§4.6): the honest prover's queries, a function of the tree; their
closed bound per node under the shape; the valid generator and the leanXMSS leaf's; each at Lean's
three axioms.
-/

open LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Rom
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Node
open LeanVM.E2E LeanVM.E2E.Complete
open OracleComp OracleSpec

/-! ## The prover's queries -/

example (ρ pfuel : ℕ) (T : HonestTree) :
    IsTotalQueryBound (honestProverComp ρ pfuel T) (T.proverQueries ρ pfuel) :=
  isTotalQueryBound_honestProverComp ρ pfuel T

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_honestProverComp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isTotalQueryBound_honestProverComp

example (ρ pfuel : ℕ) (c : Claims) (xs : List (Holder LeanXmss.Signature))
    (ss : List (Holder Sphincs.Signature)) (ds : List (Holder Da.Witness))
    (kids : List HonestTree) :
    (HonestTree.node c xs ss ds kids).proverQueries ρ pfuel =
      (kids.attach.map fun k ↦ k.1.proverQueries ρ pfuel).sum +
        nodeOwnQueries pfuel kids.length c xs ss ds :=
  HonestTree.proverQueries_node

/-! ## The closed bound -/

example (c : Claims) (xs : List (Holder LeanXmss.Signature))
    (ss : List (Holder Sphincs.Signature)) (ds : List (Holder Da.Witness))
    (kids : List HonestTree) :
    HonestTree.ShapeOK (.node c xs ss ds kids) ↔
      kids.length ≤ 16 ∧ c.xmss.length + c.sphincs.length ≤ 2 ^ 16 ∧
        (Hints.direct c.da ds).length ≤ 1 ∧
        ∀ dw, Holder.direct dw ∈ ds → dw.rows.length ≤ LeanDa.maxRows :=
  Iff.rfl

example {T : HonestTree} (h : HonestTree.ShapeOK T) : HonestTree.KidsLe16 T :=
  h.kidsLe16

example (pfuel : ℕ) : nodeQueries pfuel =
    deferQueries 16 + (7 + ((2 + checksBound) +
      (3 + (leanVmCost * proverFactor costHeight pfuel +
        (leanVmCost * proverFactor costHeight pfuel + 16 * 7))))) := rfl

example (pfuel : ℕ) : nodeQueries pfuel = 45507690 + 26420 * (2 ^ 27 + pfuel + 1) :=
  nodeQueries_eq pfuel

example (ρ pfuel : ℕ) (T : HonestTree) (hs : T.AllNodes HonestTree.ShapeOK) :
    T.proverQueries ρ pfuel ≤ T.size * nodeQueries pfuel :=
  proverQueries_le ρ pfuel T hs

/-- info: 'LeanVM.E2E.Complete.proverQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proverQueries_le

/-! ## Valid generators -/

example (ρ pfuel N QP : ℕ) (gen : OracleComp HashSpec (Option HonestTree)) :
    ValidGen ρ pfuel N QP gen ↔
      (∀ T, some T ∈ support gen → T.proverQueries ρ pfuel ≤ QP) ∧
      ∀ z ∈ support ((simulateQ loggedRO gen).run []), ∀ T, z.1 = some T →
        T.size ≤ N ∧ T.AllNodes HonestTree.ShapeOK ∧
          ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) →
            T.Valid Ht ∧ T.WithinLimitsN Ht ρ pfuel :=
  Iff.rfl

example (H : Bytes → Digest) (ρ pfuel : ℕ) {c : Claims}
    {xs : List (Holder LeanXmss.Signature)} {ss : List (Holder Sphincs.Signature)}
    {ds : List (Holder Da.Witness)}
    (h : End.Limits ⟨c, leafDefer⟩ ⟨[], xs, ss, ds, noHints⟩ ∧
      B2C.b2cBudget'.size (End.work ⟨c, leafDefer⟩ ⟨[], xs, ss, ds, noHints⟩) ≤ 2 ^ 28) :
    (HonestTree.node c xs ss ds []).WithinLimitsN H ρ pfuel :=
  withinLimitsN_leaf H ρ pfuel h

/-- info: 'LeanVM.E2E.Complete.withinLimitsN_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinLimitsN_leaf

example (pfuel : ℕ) : xmssLeafQueries pfuel =
    7 + (2 + (5 + xmssVerifyBound + (1 + 3 * 22 + 3 * (2 * blake2sR1csLogSize)))) + 3 +
      2 * (leanVmCost * proverFactor costHeight pfuel) := rfl

example (ρ pfuel : ℕ) : ValidGen ρ pfuel 1 (xmssLeafQueries pfuel) xmssLeafGen :=
  validGen_xmssLeafGen ρ pfuel

/-- info: 'LeanVM.E2E.Complete.validGen_xmssLeafGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms validGen_xmssLeafGen
