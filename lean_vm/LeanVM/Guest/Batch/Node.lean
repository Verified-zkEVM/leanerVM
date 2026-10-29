/-
  LeanVM.Guest.Batch.Node

  A node's batching as the statement states it (`NodeRel`: the program `batchOf` run on the stream
  of the children's claims and the hints) is the guest program's transcript `Node.batch`.
-/

module

public import LeanVM.Guest.Batch.Prog
public import LeanVM.Protocol.Verifier.DeferredShape

/-!
# A node's batching

`batchRun_batchOf_iff`: for children of the bytecode's shapes and a deferred claim `d` of its
shape, the batching program `batchOf (· = d)` accepts the stream of the children's claims and the
hints exactly where `Node.batch` defers `d`. The program reads the sumcheck's `log₂ |bytecode|`
rounds; an accepting run consumes the whole stream, so the hints have that many rounds
(`rounds_length_of_accepts`), and `batch` defers a claim at a point of as many coordinates as the
hints have rounds.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

theorem rsRun_length : ∀ (rounds : List (E × E)) (claim : E) (sp : Sponge),
    (rsRun rounds claim sp).1.1.length = rounds.length
  | [], _, _ => rfl
  | _ :: rest, _, _ => by simp [rsRun, rsRun_length rest]

/-- **The rounds read their messages**: a run of `k` rounds, then a continuation, on a stream
reads `2k` scalars and runs the continuation on the rest. -/
theorem runD_roundsProg_bind {β : Type} (f : List E × E → Prog β) :
    ∀ (k : ℕ) (claim : E) (sp : Sponge) (zs : List E) (os : List Opening)
      (roots : List (Digest × ℕ × ℕ)) {r : β × St},
      runD ((roundsProg claim k).bind f) ⟨sp, zs, os, roots⟩ = some r →
        2 * k ≤ zs.length ∧ ∃ x sp', runD (f x) ⟨sp', zs.drop (2 * k), os, roots⟩ = some r
  | 0, claim, sp, zs, os, roots, r, h => ⟨by omega, _, _, h⟩
  | k + 1, claim, sp, zs, os, roots, r, h => by
    rcases zs with _ | ⟨g1, _ | ⟨gInf, zs⟩⟩
    · exact absurd h (by simp [roundsProg, Prog.readE, Prog.bind_eq, Prog.bind, runD, Compile.run])
    · exact absurd h (by simp [roundsProg, Prog.readE, Prog.bind_eq, Prog.bind, runD, Compile.run])
    · simp only [roundsProg, Prog.readE, Prog.sampleE, Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc,
        Prog.ret_bind] at h
      obtain ⟨hlen, x, sp', hx⟩ := runD_roundsProg_bind _ k _ _ zs os roots h
      have e : (g1 :: gInf :: zs).drop (2 * (k + 1)) = zs.drop (2 * k) := by
        rw [show 2 * (k + 1) = 2 * k + 2 by ring]
        rfl
      rw [e]
      exact ⟨by simp; omega, _, sp', hx⟩

/-- The stream of the batching, its parts. -/
theorem batchStream_eq (cs : List ChildClaims) (h : BatchHints) :
    batchStream cs h = headCells cs.length ++ (cs.flatMap childCells ++
      (h.bytecodeRounds.flatMap (fun g ↦ [g.1, g.2]) ++ [h.bytecodeValue])) := by
  simp only [batchStream, batchWords, List.append_assoc]

theorem length_rounds_flat (rounds : List (E × E)) :
    (rounds.flatMap fun g ↦ [g.1, g.2]).length = 2 * rounds.length := by
  induction rounds with
  | nil => rfl
  | cons g rest ih => simp [ih]; ring

/-- The run of the batching from its seed, with the count's and the children's cells read. -/
theorem runD_batchOf (check : DeferredClaim → Prop) {bytecode : List K}
    {cs : List ChildClaims} (hs : ∀ c ∈ cs, ChildShaped bytecode c) (rest : List E) :
    runD (batchOf check bytecode cs.length)
        ⟨⟨batchSeed, []⟩, headCells cs.length ++ (cs.flatMap childCells ++ rest), [], []⟩ =
      runD (batchRest check bytecode cs) ⟨batchSponge cs, rest, [], []⟩ := by
  have hsp : batchSponge cs = obsAll (obsAll ⟨batchSeed, []⟩ (headCells cs.length))
      (cs.flatMap childCells) := obsAll_append _ _ _
  rw [batchOf, runD_bind_of_runsTo (runsTo_readN' _ (headCells cs.length) (n := rateScalars) rfl),
    ← List.nil_append (List.flatMap childCells cs ++ rest),
    runD_bind_of_runsTo (runsTo_require rfl _), batchProg,
    runD_bind_of_runsTo (runsTo_readChildren hs _), ← hsp]

/-- The tail of the batching: the final value read, the check, acceptance. -/
theorem runD_tail_accepts {c : E → Prop} {dc : DecidablePred c} {sp : Sponge} {zs : List E}
    {s : St} (h : runD (Prog.readE >>= fun bv ↦ @Prog.require (c bv) (dc bv) >>= fun _ ↦
      (pure true : Prog Bool)) ⟨sp, zs, [], []⟩ = some (true, s)) (hs : s.stream = []) :
    zs.length = 1 := by
  rcases zs with _ | ⟨v, ws⟩
  · exact absurd h (by simp [Prog.readE, Prog.bind_eq, Prog.bind, runD, Compile.run])
  · have e := runD_bind_of_runsTo (f := fun bv ↦ @Prog.require (c bv) (dc bv) >>= fun _ ↦
      (pure true : Prog Bool)) (runsTo_readE sp v) ws [] []
    simp only [List.singleton_append] at e
    rw [e, @runD_require_true (c v) (dc v)] at h
    split_ifs at h with hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      have hw : ws = [] := by rw [← h.2] at hs; exact hs
      rw [hw]
      rfl

/-- **An accepting run reads the hints' rounds as the program's**: the hints have
`log₂ |bytecode|` rounds. -/
theorem rounds_length_of_accepts {check : DeferredClaim → Prop} {bytecode : List K}
    {cs : List ChildClaims} {h : BatchHints} (hs : ∀ c ∈ cs, ChildShaped bytecode c)
    (hacc : Id.run (batchRun (m := Id) keccak256 keccakF (batchOf check bytecode cs.length)
      ⟨batchStream cs h, []⟩) = true) :
    h.bytecodeRounds.length = Nat.log2 bytecode.length := by
  change (match runD (batchOf check bytecode cs.length)
      ⟨⟨batchSeed, []⟩, batchStream cs h, [], []⟩ with
    | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
    | _ => false) = true at hacc
  rw [batchStream_eq, runD_batchOf check hs, batchRest,
    ← List.nil_append (List.flatMap _ _ ++ _), runD_bind_of_runsTo (runsTo_sampleL _ _)] at hacc
  generalize hR : runD (roundsProg _ _ >>= _) _ = R at hacc
  rcases R with _ | ⟨_ | _, s⟩
  · simp at hacc
  · simp at hacc
  · simp only [Bool.and_eq_true, List.isEmpty_iff] at hacc
    obtain ⟨hle, x, sp', hx⟩ := runD_roundsProg_bind _ _ _ _ _ _ _ hR
    have h1 := runD_tail_accepts hx hacc.1
    simp only [List.length_drop, List.length_append, length_rounds_flat, List.length_singleton]
      at h1 hle
    omega

/-- **A node's batching is `Node.batch`**: for children of the bytecode's shapes and a deferred
claim of its shape, the program accepts the stream exactly where `batch` defers that claim. -/
theorem batchRun_batchOf_iff {bytecode : List K} {cs : List ChildClaims} {h : BatchHints}
    {d : DeferredClaim} (hs : ∀ c ∈ cs, ChildShaped bytecode c) (hd : d.Shaped bytecode) :
    Id.run (batchRun (m := Id) keccak256 keccakF (batchOf (· = d) bytecode cs.length)
      ⟨batchStream cs h, []⟩) = true ↔ batch cs h = some d := by
  have key : h.bytecodeRounds.length = Nat.log2 bytecode.length →
      (Id.run (batchRun (m := Id) keccak256 keccakF (batchOf (· = d) bytecode cs.length)
        ⟨batchStream cs h, []⟩) = true ↔ batch cs h = some d) := by
    intro hr
    change (match runD (batchOf (· = d) bytecode cs.length)
        ⟨⟨batchSeed, []⟩, batchStream cs h, [], []⟩ with
      | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
      | _ => false) = true ↔ _
    rw [batchStream_eq, runD_batchOf _ hs, batchRest,
      ← List.nil_append (List.flatMap _ _ ++ _),
      runD_bind_of_runsTo (runsTo_sampleL _ _),
      runD_bind_of_runsTo (runsTo_roundsProg h.bytecodeRounds _ _ hr),
      ← List.append_nil [h.bytecodeValue],
      runD_bind_of_runsTo (runsTo_readE _ _), runD_require_true, batch_eq']
    simp only [lambdasB, claimB, spB]
    split_ifs <;> simp_all
  constructor
  · intro hacc
    exact (key (rounds_length_of_accepts hs hacc)).mp hacc
  · intro hb
    have hr : h.bytecodeRounds.length = Nat.log2 bytecode.length := by
      have e := hb
      rw [batch_eq'] at e
      split_ifs at e
      have := congrArg (fun c : DeferredClaim ↦ c.bytecodePoint.length) (Option.some.inj e)
      simp only [rsRun_length] at this
      rw [this]
      exact hd
    exact (key hr).mpr hb

/-! ## `NodeRel` with the guest program's transcript -/

/-- `NodeRel` with the batching as the guest program's transcript (`Node.batch`). -/
def _root_.LeanVM.Node.NodeRelB (bytecode : List K) (seed : Digest) (s : NodeStatement)
    (w : NodeWitness) : Prop :=
  s.defer.Shaped bytecode ∧
  (∀ c ∈ w.children, c.statement.defer.Shaped bytecode ∧
    verifyDeferred bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true) ∧
  List.Forall₂ (Held (fun (c : XmssClaim) σ ↦ xmssVerify c.1 c.2 σ = true) Claims.xmss
    w.children) s.claims.xmss w.xmss ∧
  List.Forall₂ (Held (fun (c : SphincsClaim) σ ↦ sphincsVerify c.1 c.2 σ = true) Claims.sphincs
    w.children) s.claims.sphincs w.sphincs ∧
  (match w.da with
    | some (c, m) => s.claims.da = daClaimDigest c ∧ m.Opens c.daRoot c.membershipVectorDigest
    | none => s.claims.da = zeroDigest ∨ ∃ c ∈ w.children, c.statement.claims.da = s.claims.da) ∧
  if w.children = [] then s.defer.AtZero bytecode
  else batch (w.children.map fun c ↦
    ⟨statementDigest seed c.statement, c.fresh, c.statement.defer⟩) w.hints = some s.defer

/-- **`NodeRel` is `NodeRelB`**: the statement's batching program accepts the node's stream
exactly where the guest program's transcript defers the node's claim. -/
theorem _root_.LeanVM.Node.nodeRel_iff {bytecode : List K} {seed : Digest} {s : NodeStatement}
    {w : NodeWitness} : NodeRel bytecode seed s w ↔ NodeRelB bytecode seed s w := by
  unfold NodeRel NodeRelB
  refine and_congr_right fun h1 ↦ and_congr_right fun h2 ↦ and_congr_right fun _ ↦
    and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  split
  · exact Iff.rfl
  · have hs : ∀ c ∈ w.children.map (fun c : Child ↦ (⟨statementDigest seed c.statement, c.fresh,
        c.statement.defer⟩ : ChildClaims)), ChildShaped bytecode c := by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact ⟨verifyDeferred_shaped (h2 c' hc').2, (h2 c' hc').1⟩
    have e := batchRun_batchOf_iff (h := w.hints) hs h1
    rw [List.length_map] at e
    exact e

end
end LeanVM.Guest.Batch
