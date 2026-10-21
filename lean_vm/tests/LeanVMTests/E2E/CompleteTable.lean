import LeanVM.E2E.Complete.Model
import LeanVM.E2E.Complete.Candidates
import LeanVM.Protocol.EndToEnd.Blind.Complete
import LeanVM.E2E.Complete.Node
import LeanVM.E2E.Complete.Assemble
import LeanVM.E2E.Complete.NonVacuity
import LeanVM.E2E.Complete.Tree
import LeanVM.E2E.Budget

/-!
# T6-det's proved pieces, locked

Statement locks of `LeanVM/E2E/Complete/` and `LeanVM/Protocol/EndToEnd/Blind/Complete.lean`
(`docs/roadmap/t6-completeness.md`): the honest table passes V_I's precheck and table check for
every hash, its semantics is functional, the honest execution is the one V_I re-runs, an exact
encoding's candidates are its stack, and V° accepts the honest proof for every hash; with their
foundations pinned.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.E2E LeanVM.E2E.Complete

/-! ## The honest table -/

example {D : List Bytes} (I : Intermediates D) (H : Bytes → Digest)
    {rows : List BlakeRow} (h : ∀ r ∈ rows, CanonRow r ∧ ChainRow I H r) :
    tableOKWith (m := Id) (fun x ↦ (pure (H x) : Id Digest)) rows = true :=
  tableOKWith_chainRows h

example {D : List Bytes} (I : Intermediates D) (H : Bytes → Digest)
    {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecutionB (CompModel.chain I H).sem prog input t) :
    haltingRunB blakeFree prog t.image = some t ∧
      tableOKWith (m := Id) (fun x ↦ (pure (H x) : Id Digest))
        (t.blakeRows blakeFree) = true :=
  ⟨haltingRunB_of_validChain hv, tableOKWith_of_validB hv⟩

/-- info: 'LeanVM.E2E.Complete.stdChain_chainRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stdChain_chainRows

/-- info: 'LeanVM.E2E.Complete.precheck_chainRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms precheck_chainRows

/-- info: 'LeanVM.E2E.Complete.tableOKWith_chainRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableOKWith_chainRows

/-- info: 'LeanVM.E2E.Complete.chainSem_functional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainSem_functional

/-- info: 'LeanVM.E2E.Complete.haltingRunB_of_validB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms haltingRunB_of_validB

/-- info: 'LeanVM.E2E.Complete.tableOKWith_of_validB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableOKWith_of_validB

/-- info: 'LeanVM.E2E.Complete.CompModel.deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompModel.deployed

/-! ## The candidates of an honest word -/

/-- info: 'LeanVM.E2E.Complete.eq_of_mem_candidates_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_of_mem_candidates_deployed

/-! ## V° accepts the honest proof -/

/-- info: 'LeanVM.Protocol.EndToEnd.Blind.runI_blindProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Protocol.EndToEnd.Blind.runI_blindProgram

/-- info: 'LeanVM.Protocol.EndToEnd.Blind.exists_prove_verifyBlindWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Protocol.EndToEnd.Blind.exists_prove_verifyBlindWith

/-! ## V_I on honest nodes -/

/-- info: 'LeanVM.E2E.Complete.nodeHead_prove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeHead_prove

/-- info: 'LeanVM.E2E.Complete.nodeStep_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeStep_honest

/-- info: 'LeanVM.E2E.Complete.closure_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms closure_accepts

/-- info: 'LeanVM.E2E.Complete.idealVerify_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealVerify_accepts

/-- info: 'LeanVM.E2E.Complete.outerChecksWith_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerChecksWith_true

/-! ## The deferring verifier, the interfaces, T6-det -/

/-- info: 'LeanVM.E2E.Complete.verifyDeferredWith_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verifyDeferredWith_honest

/-- info: 'LeanVM.E2E.Complete.capsAgreeWith_blake2s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms capsAgreeWith_blake2s

/-- info: 'LeanVM.Semantics.committedSizeB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms committedSizeB_deployed

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealVerify_complete

/-- T6-det's statement, locked. -/
example (H : Bytes → Digest) (T : HonestTree) {ρ pfuel fuel : ℕ} (hρ : validRate ρ)
    {o : HonestOut} (hI : honestOut H ρ pfuel T = some o) (hroots : RootsInj o.entries)
    (hfuel : T.size ≤ fuel)
    (hda : ∀ c ∈ T.claims.da,
      LeanVM.Da.toBytes c.2 = Id.run (LeanVM.Da.vectorDigestOfWith (fun x ↦ (pure (H x) : Id Digest)) c.1)) :
    o.stmt.claims = T.claims ∧
      idealVerify (m := Id) (fun x ↦ (pure (H x) : Id Digest)) LeanVM.Guest.guest (idealOf o) fuel o.stmt =
        true :=
  idealVerify_complete H T hρ hI hroots hfuel hda

/-! ## L3, L4, L12, the honest step -/

/-- info: 'LeanVM.Arithmetization.constraintCompletenessB_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Arithmetization.constraintCompletenessB_rows

/-- info: 'LeanVM.Protocol.LeanIsa.m3HonestBlind_stackOfG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Protocol.LeanIsa.m3HonestBlind_stackOfG

/-- info: 'LeanVM.E2E.Complete.exists_stack_of_validB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_stack_of_validB

/-- info: 'LeanVM.E2E.Complete.nodeRel_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeRel_honest

/-- info: 'LeanVM.E2E.Complete.honestOut_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honestOut_child

/-- info: 'LeanVM.E2E.Complete.honestStep_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honestStep_isSome

/-! ## L11, the caps, L16, the tree -/

example (H : Bytes → Digest) {s0 : Digest} {bytecode : List K} {cs : List LeanVM.Node.ChildClaims}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (hcs : ∀ c ∈ cs, c.fresh.bytecodePoint.length = Nat.log2 bytecode.length ∧
      c.carried.bytecodePoint.length = Nat.log2 bytecode.length ∧
      multilinearEval (bytecode.map ofK) c.fresh.bytecodePoint = c.fresh.bytecodeValue ∧
      multilinearEval (bytecode.map ofK) c.carried.bytecodePoint = c.carried.bytecodeValue)
    (hw : (honestWeights H s0 bytecode cs).1 ≠ 0 ∨ (honestWeights H s0 bytecode cs).2 ≠ 0) :
    ∃ d, LeanVM.Node.batchWith (fun x ↦ some (H x)) s0 cs (honestHints H s0 bytecode cs) = some (some d) ∧
      d.BytecodeHolds bytecode :=
  batchWith_honestHints H hb hcs hw

example (H : Bytes → Digest) (S : Strategy) (fuel : ℕ) {c : FixedClaims} {bytecode : List K}
    {publicInput seed : Digest} {π : Proof}
    (hπ : prove H (deferredProgram c bytecode publicInput) S seed fuel = some π)
    {r : Bool × Digest × List Ev}
    (hfs : fsRun H S fuel (deferredProgram c bytecode publicInput) seed [] = some r) :
    ∀ b ∈ queriesOfWith H (deferredProgram c bytecode publicInput)
      ⟨seed, π.stream, π.openings, []⟩, BatchAgreesWith H b.1 b.2 :=
  queriesOfWith_deferred_honest H S fuel hπ hfs

example {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    {φ : ∀ {α : Type}, m α → n α} (hφ : IsMorphism @φ) (H : Bytes → m Digest) (prog : Program)
    (ip : IdealProof) (fuel : ℕ) (s : LeanVM.Node.NodeStatement) :
    φ (idealVerify H prog ip fuel s) = idealVerify (fun x ↦ φ (H x)) prog ip fuel s :=
  idealVerify_natural hφ H prog ip fuel s

example {nx ns : ℕ} {b : Type → Type} [Monad b] [LawfulMonad b] (impl : QueryImpl GameSpec b)
    (H : Bytes → Digest)
    (himpl : ∀ x, simulateQ impl (liftM (LeanVM.HashSpec.query x) : OracleComp GameSpec Digest) = pure (H x))
    (budget : ℕ) (prog : Program) (ip : IdealProof) (fuel : ℕ) (s : LeanVM.Node.NodeStatement)
    (st : SignState nx ns) :
    simulateQ impl (((idealVerify (budgetedQuery budget) prog ip fuel s).run).run st) =
      pure (if queryCount H prog ip fuel s = 0 ∨ st.spent + queryCount H prog ip fuel s ≤ budget
        then (some (Id.run (idealVerify (fun x ↦ (pure (H x) : Id Digest)) prog ip fuel s)),
          { st with spent := st.spent + queryCount H prog ip fuel s })
        else (none, { st with spent := max st.spent budget })) :=
  run_idealVerify_budgetedQuery impl H himpl budget prog ip fuel s st

example (H : Bytes → Digest) (ρ pfuel : ℕ) (hL2 : GuestCompleteModel) (hρ : validRate ρ)
    (T : HonestTree) (hv : T.AllNodes (HonestTree.ValidAt H)) (hlim : T.WithinLimits H ρ pfuel)
    (hpow : T.PowFound H ρ pfuel) (hw : T.WeightsNonzero H ρ pfuel) :
    ∃ o, honestOut H ρ pfuel T = some o :=
  honestOut_isSome H ρ pfuel hL2 hρ T hv hlim hpow hw

example (H : Bytes → Digest) (ρ pfuel : ℕ) (hL2 : GuestCompleteModel) (T : HonestTree)
    {fuel : ℕ} (hρ : validRate ρ) (hv : T.Valid H) (hlim : T.WithinLimits H ρ pfuel)
    (hpow : T.PowFound H ρ pfuel) (hw : T.WeightsNonzero H ρ pfuel)
    (hroots : T.RootsInjAt H ρ pfuel) (hfuel : T.size ≤ fuel) :
    ∃ s ip, honestIdeal H ρ pfuel T = some (s, ip) ∧ s.claims = T.claims ∧
      idealVerify (m := Id) (fun x ↦ (pure (H x) : Id Digest)) LeanVM.Guest.guest ip fuel s = true :=
  idealVerify_complete' H ρ pfuel hL2 T hρ hv hlim hpow hw hroots hfuel

/-- info: 'LeanVM.E2E.Complete.batchWith_honestHints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms batchWith_honestHints

/-- info: 'LeanVM.E2E.Complete.qRange_deferredProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qRange_deferredProgram

/-- info: 'LeanVM.E2E.Complete.queriesOfWith_deferred_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms queriesOfWith_deferred_honest

/-- info: 'LeanVM.E2E.Complete.exists_deferred_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_deferred_honest

/-- info: 'LeanVM.E2E.idealVerify_natural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.idealVerify_natural

/-- info: 'LeanVM.E2E.run_idealVerify_budgetedQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.run_idealVerify_budgetedQuery

/-- info: 'LeanVM.E2E.Complete.honestOut_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honestOut_isSome

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealVerify_complete'

/-- info: 'LeanVM.E2E.Complete.idealVerify_complete_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealVerify_complete_budget
