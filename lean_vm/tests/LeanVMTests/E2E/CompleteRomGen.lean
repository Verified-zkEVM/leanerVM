import LeanVM.E2E.Complete.Rom.Gen

/-!
# T6-prob's inhabitant, locked

Statement locks of `LeanVM/E2E/Complete/Rom/Gen.lean` (`docs/roadmap/t6-prob.md` §4.6, P7): the
generator `xmssLeafGen` (honest leanXMSS key generation, one signature on the zero message, the leaf
holding it) outputs leaves valid and within the limits at every hash agreeing with the oracle's
log, with a total query bound; leanXMSS's correctness at every hash; each at Lean's three axioms.
-/

open LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Rom
open LeanVM.Protocol.Compile.Rom
open LeanVM.Node LeanVM.Guest LeanVM.E2E LeanVM.E2E.Complete
open OracleComp OracleSpec

/-! ## The generator -/

noncomputable example : OracleComp HashSpec (Option HonestTree) := xmssLeafGen

example (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    xmssLeaf pk σ = .node ⟨[(pk, 0)], [], []⟩ [.direct σ] [] [] [] := rfl

/-! ## leanXMSS's correctness at every hash -/

example (f : LeanXmss.HashInput → LeanXmss.HashOutput) (pk : LeanXmss.PublicKey)
    (σ : LeanXmss.Signature) (h : xgEv f xgCore = some (pk, σ)) :
    xgEv f (LeanXmss.Concrete.verify pk 0 σ) = true :=
  xg_correct f pk σ h

/-- info: 'LeanVM.E2E.Complete.xg_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xg_correct

/-! ## The generator's outputs -/

example : ∀ z ∈ support ((simulateQ loggedRO xmssLeafGen).run []), ∀ T, z.1 = some T →
    ∃ pk σ, T = .node ⟨[(pk, 0)], [], []⟩ [.direct σ] [] [] [] ∧
      ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) → T.Valid Ht :=
  xmssLeafGen_spec

/-- info: 'LeanVM.E2E.Complete.xmssLeafGen_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssLeafGen_spec

example (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    End.Limits ⟨⟨[(pk, 0)], [], []⟩, leafDefer⟩ ⟨[], [.direct σ], [], [], noHints⟩ ∧
      B2C.b2cBudget'.size
        (End.work ⟨⟨[(pk, 0)], [], []⟩, leafDefer⟩ ⟨[], [.direct σ], [], [], noHints⟩) ≤ 2 ^ 28 :=
  xmssLeaf_limits pk σ

/-- info: 'LeanVM.E2E.Complete.xmssLeaf_limits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssLeaf_limits

example (ρ pfuel : ℕ) : ∀ z ∈ support ((simulateQ loggedRO xmssLeafGen).run []), ∀ T,
    z.1 = some T → T.size ≤ 1 ∧ ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) →
      T.Valid Ht ∧ T.WithinLimitsBudget Ht ρ pfuel :=
  xmssLeafGen_valid ρ pfuel

/-- info: 'LeanVM.E2E.Complete.xmssLeafGen_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssLeafGen_valid

/-! ## The generator's queries -/

example : IsTotalQueryBound xmssLeafGen (2 ^ 33 + 53739486) :=
  xmssLeafGen_queries_eq ▸ isTotalQueryBound_xmssLeafGen

/-- info: 'LeanVM.E2E.Complete.isTotalQueryBound_xmssLeafGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isTotalQueryBound_xmssLeafGen
