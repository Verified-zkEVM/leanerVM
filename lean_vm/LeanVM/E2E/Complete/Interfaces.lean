/-
  LeanVM.E2E.Complete.Interfaces

  The two statements T6-det assembles from and the packages L2 and L9 prove: the guest's
  completeness over a completeness model, and the decoding of its honest children; with what
  they mention, the counts under a semantics and the caps' agreement under a hash.
-/

module

public import LeanVM.E2E.Complete.Model
public import LeanVM.Guest.EndCompleteFinal
public import LeanVM.Arithmetization.CompletenessB.Count

/-!
# T6-det's interfaces

`docs/roadmap/t6-completeness.md` decomposes T6-det. Two of its packages are proved elsewhere and
enter its assembly as hypotheses, in exactly the shapes defined here:

* **L2, `GuestCompleteModel`** — the guest's completeness over every completeness model
  `CM` (`CompModel`): from `NodeRelWith CM.H` within the deployed limits, the caps' agreement
  and the budget, a valid execution under `CM.sem`, of committed size at most `2^28` (counted
  under `CM.sem`, `committedSizeB`), together with frames `fr` at which V_I's decoder reads back
  the witness's children (`DecodeHonest`). At `CompModel.deployed` its first two conclusions are
  `guest_complete`'s.
* **L9, `DecodeHonest fr t w`** — decoding the execution's memory under its own table
  semantics (`tableSem (t.blakeRows blakeFree)`, decision E2E-3), at the frames `fr` the
  idealized proof names (decision E2E-5), gives the children of `w`: their statements and
  proofs, which is all V_I reads of them, with V_I's decoder `End.decodeAt`.

What they mention:

* `runCountB`, `Trace.countB`, `Trace.committedSizeB`: the instruction counts and the committed
  size of an execution stepping under a semantics `S` (the deployed `Trace.count` stops at a
  `BLAKE2S` step that is no compression); at `blakeDeployed` they are the deployed ones
  (`committedSizeB_deployed`);
* `CapsAgreeWith Ht seed w`: the deployed `CapsAgree` with every hash `Ht` (`queriesOfWith`,
  `NodeIsWith`, `BatchAgreesWith`); at `blake2sBytes` it is `CapsAgree` (`capsAgreeWith_blake2s`).
  The completeness model's answered hash `CM.H` is partial; the caps' hypothesis is stated with a
  total `Ht` that `CM.H` agrees with where it answers.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Guest.B1

@[expose] public section

/-! ## The caps' agreement under a hash -/

/-- **The query steps of a run with the hash `Ht`** (`B1.queriesOf` with `Ht`). -/
def queriesOfWith (Ht : Bytes → Digest) {α : Type} : Prog α → St → List (ℕ × List (ℕ × Opening))
  | .ret _, _ => []
  | .fail, _ => []
  | .read k, s => match s.stream with
    | [] => []
    | x :: xs => queriesOfWith Ht (k x)
        { s with cv := absorbBlock (m := Id) Ht s.cv (blockOf x 1), stream := xs }
  | .sample k, s =>
    let cv := absorbBlock (m := Id) Ht s.cv (blockOf 0 2)
    queriesOfWith Ht (k (challengeOf cv)) { s with cv := cv }
  | .grind bits k, s => match s.stream with
    | [] => []
    | n :: xs =>
      let base := absorbBlock (m := Id) Ht s.cv (blockOf 0 3)
      let d := absorbBlock (m := Id) Ht base (blockOf n 4)
      let cv := absorbBlock (m := Id) Ht s.cv (blockOf n 4)
      if powOk bits n d then queriesOfWith Ht k { s with cv := cv, stream := xs } else []
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs =>
      let cv0 := absorbBlock (m := Id) Ht s.cv (blockOf x0 1)
      let cv1 := absorbBlock (m := Id) Ht cv0 (blockOf x1 1)
      match digestOfScalars (x0, x1) with
      | some root =>
        queriesOfWith Ht k
          { s with cv := cv1, stream := xs, roots := s.roots ++ [(root, height, width)] }
      | none => []
    | _ => []
  | .query i ps k, s => match s.roots[i]? with
    | none => []
    | some (root, height, width) =>
      match openAll (m := Id) Ht root height width ps s.openings with
      | some (rows, rest) =>
        (height, ps.zip s.openings) :: queriesOfWith Ht (k rows) { s with openings := rest }
      | none => []

/-- **The opening `a` gives the heap node `v` the digest `d`, with the hash `Ht`**
(`B1.NodeIs`). -/
def NodeIsWith (Ht : Bytes → Digest) (depth : ℕ) (a : ℕ × Opening) (v : ℕ) (d : Digest) : Prop :=
  (∃ l ≤ depth, v = heapNode depth a.1 l ∧
      d = climb (m := Id) Ht (Ht (a.2.leaf.flatMap kBytes)) a.1 (a.2.path.take l)) ∨
    ∃ l < depth, v = sibNode depth a.1 l ∧ d = a.2.path.getD l default

/-- The openings of one step agree wherever they meet, with the hash `Ht`. -/
def BatchAgreesWith (Ht : Bytes → Digest) (depth : ℕ) (qs : List (ℕ × Opening)) : Prop :=
  ∀ a ∈ qs, ∀ b ∈ qs, ∀ v d d', NodeIsWith Ht depth a v d → NodeIsWith Ht depth b v d' → d = d'

/-- **A child's openings agree in the guest's Merkle caps, with the hash `Ht`** (`End.CapsAgree`
with `Ht`): at every query step of each child's deferring verifier under the node's seed. -/
def CapsAgreeWith (Ht : Bytes → Digest) (seed : Digest) (w : NodeWitness) : Prop :=
  ∀ c ∈ w.children,
    ∀ b ∈ queriesOfWith Ht
      (Verifier.deferredProgram c.fresh End.bytecode
        (Id.run (statementDigestWith (m := Id) Ht seed c.statement)))
      ⟨Ht (digestBytes seed ++ digestBytes (Id.run (statementDigestWith (m := Id) Ht seed
          c.statement))), c.proof.stream, c.proof.openings, []⟩,
    BatchAgreesWith Ht b.1 b.2

theorem queriesOfWith_blake2s {α : Type} :
    ∀ (p : Prog α) (s : St), queriesOfWith blake2sBytes p s = queriesOf p s
  | .ret _, _ => rfl
  | .fail, _ => rfl
  | .read k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨x, xs⟩
    · rfl
    · simp only [queriesOfWith, queriesOf, queriesOfWith_blake2s]
  | .sample k, s => by simp only [queriesOfWith, queriesOf, queriesOfWith_blake2s]
  | .grind bits k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨n, xs⟩
    · rfl
    · simp only [queriesOfWith, queriesOf, queriesOfWith_blake2s]
  | .commit ht w k, ⟨cv, stream, os, roots⟩ => by
    rcases stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
    · rfl
    · rfl
    · simp only [queriesOfWith, queriesOf]
      rcases digestOfScalars (x0, x1) with _ | root
      · rfl
      · simp only [queriesOfWith_blake2s]
  | .query i ps k, ⟨cv, stream, os, roots⟩ => by
    simp only [queriesOfWith, queriesOf]
    rcases roots[i]? with _ | ⟨root, height, width⟩
    · rfl
    · simp only
      rcases openAll (m := Id) blake2sBytes root height width ps os with _ | ⟨rows, rest⟩
      · rfl
      · simp only [queriesOfWith_blake2s]

/-- **At BLAKE2s the caps' agreement is the deployed one.** -/
theorem capsAgreeWith_blake2s (seed : Digest) (w : NodeWitness) :
    CapsAgreeWith blake2sBytes seed w ↔ End.CapsAgree seed w := by
  have hn : ∀ depth a v d, NodeIsWith blake2sBytes depth a v d ↔ NodeIs depth a v d :=
    fun _ _ _ _ ↦ Iff.rfl
  simp only [CapsAgreeWith, End.CapsAgree, BatchAgreesWith, BatchAgrees, hn, queriesOfWith_blake2s]
  rfl

/-! ## The interfaces -/

/-- The frames an idealized proof names for a node's located calls, by callee and words
(decision E2E-5); `none` where it names none. -/
abbrev Frames : Type := String → List E → Option ℕ

/-- **L9: the honest children decode.** Decoding the execution's memory under its own table
semantics at the frames `fr` gives the children of `w`, their statements and proofs. -/
def DecodeHonest (fr : Frames) (t : Trace Guest.guest) (w : NodeWitness) : Prop :=
  ((End.decodeAt (Value.tableSem (t.blakeRows blakeFree)) fr t.image).witness.children.map
      fun c ↦ (c.statement, c.proof)) = w.children.map fun c ↦ (c.statement, c.proof)

/-- **L2: the guest's completeness over a completeness model.** For every completeness model
`CM` and total hash `Ht` it agrees with where it answers: a node relation with every hash
answered by `CM.H` (the batching from the baked start `aggSeedD`, the baked DA padding), within
the deployed limits, the caps agreeing under `Ht`, and the node's work within the deployed
budget, has a valid execution of the guest under `CM.sem` on the statement's answered digest, of
committed size at most `2^28` under `CM.sem`, and frames at which V_I's decoder (`decodeAt`)
reads back its children. -/
def GuestCompleteModel : Prop :=
  ∀ (CM : CompModel) (Ht : Bytes → Digest), (∀ x d, CM.H x = some d → d = Ht x) →
    ∀ (seed : Digest) (s : NodeStatement) (w : NodeWitness) (pi : Digest),
      statementDigestWith CM.H seed s = some pi →
      NodeRelWith CM.H Main.aggSeedD Main.daPadCell Main.daPadRow End.bytecode seed s w →
      End.Limits s w → CapsAgreeWith Ht seed w →
      B2C.b2cBudget'.size (End.work s w) ≤ 2 ^ 28 →
      ∃ (t : Trace Guest.guest) (fr : Frames),
        ValidExecutionB CM.sem Guest.guest (End.publicInputOf pi) t ∧
          t.committedSizeB CM.sem ≤ 2 ^ 28 ∧ DecodeHonest fr t w

end
end LeanVM.E2E.Complete
