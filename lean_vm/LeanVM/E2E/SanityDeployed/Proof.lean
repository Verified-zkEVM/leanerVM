/-
  LeanVM.E2E.SanityDeployed.Proof

  The deployed honest proof of a node (the full verifier's honest strategy, Flock included): what
  V_I reads of it, and the deferring verifier accepting it with the fixed polynomials' true values
  read off its own run.
-/

module

public import LeanVM.E2E.Complete.Deferred
public import LeanVM.E2E.Complete.Stream
public import LeanVM.Protocol.EndToEnd.Completeness

/-!
# The deployed honest proof

The deployed prover proves a node's stack with the full verifier's honest strategy
(`Complete.leanVmProver`, the phases of `Protocol/EndToEnd/Complete`, Flock included), compiled
by `prove` with the hash `H`. This module gives the two facts about that proof the deployed
sanity theorem needs beyond its acceptance (`runProof_prove`):

* `prove_stream_head_dep`, `nodeHead_prove_dep`: its head is the honest announcement, then the
  root of the stack's word (the full verifier's analogue of `Complete.nodeHead_prove`);
* `exists_deferred_dep`: the deferring verifier (`deferredProgram c`) accepts the same proof with
  the claims `c` read off the proof's own run (`freshOfDep`: the bytecode's value and the
  matrices' value the deployed verifier computes there), and those claims are true
  (`FixedClaims.Holds`): along the run the two programs agree (`FsSame`), each hole returning
  what the deployed verifier computes.
-/

namespace LeanVM.E2E.SanityDeployed

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.Blake2sHash LeanVM.E2E.Complete

@[expose] public section

/-! ## The head of the deployed honest proof -/

/-- **The head of the deployed honest proof**: the honest announcement, then the two scalars of
the root of the stack's word at the height `commitStack` announces, then the rest. -/
theorem prove_stream_head_dep (H : Bytes → Digest) {prog : Program} {s : Sizes} {ρ : ℕ}
    {q : Column (leanIsaμ prog s)} {input : PublicInput} (hs : s.Admissible prog)
    (hρ : validRate ρ) {seed : Digest} {fuel : ℕ} {π : Proof}
    (hπ : prove H (leanVmProgram (bytecodeWords prog) (publicDigest input))
      (leanVmProver prog s ρ q) seed fuel = some π) :
    ∃ level rest tail, deriveConfig (leanIsaμ prog s) ρ = some (level :: rest) ∧
      π.stream = announce s ρ ++
        ((digestScalars (treeRoot H (stackHeight (leanIsaμ prog s) level)
            (stackWord (leanIsaμ prog s) q))).1 ::
          (digestScalars (treeRoot H (stackHeight (leanIsaμ prog s) level)
            (stackWord (leanIsaμ prog s) q))).2 :: tail) := by
  obtain ⟨q₀, rest, hc, -⟩ := exists_ladder (whirAdmissible prog hs hρ)
  obtain ⟨f, hf, hfa⟩ := readSizes_honest prog hs hρ
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hπ
  set S := leanVmProver prog s ρ q
  set W := stackWord (leanIsaμ prog s) q
  obtain ⟨K, hscript⟩ : ∃ K : Unit → Script Unit,
      Protocol.EndToEnd.Complete.honestProver prog s ρ q (leanVmPhases prog s q) =
        (Script.sendList (announce s ρ)).bind fun _ ↦ (Script.commitS W).bind K := by
    exact ⟨_, by
      simp only [Protocol.EndToEnd.Complete.honestProver, honestRun, Script.bind_eq,
        script_bind_assoc]
      rfl⟩
  have hmsg : ∀ i (hi : i < (announce s ρ).length),
      S.msg ([] ++ ((announce s ρ).take i).map Ev.read) = (announce s ρ)[i] := by
    intro i hi
    show (Protocol.EndToEnd.Complete.honestProver prog s ρ q (leanVmPhases prog s q)).msgAt
      ((((announce s ρ).take i).map Ev.read).drop 0) = _
    rw [List.drop_zero, hscript]
    exact msgAt_sendList_bind _ _ i hi
  have hword : S.word ([] ++ (announce s ρ).map Ev.read) = W := by
    show (Protocol.EndToEnd.Complete.honestProver prog s ρ q (leanVmPhases prog s q)).wordAt
      ((((announce s ρ).map Ev.read)).drop 0) = _
    have hw := walk_sendList_bind (fun _ ↦ (Script.commitS W).bind K) (announce s ρ)
      (announce s ρ).length le_rfl
    rw [List.take_length, List.drop_length] at hw
    rw [List.drop_zero, hscript, Script.wordAt, hw]
    rfl
  obtain ⟨g, k, hP, hk⟩ : ∃ (g : Verifier.Layout × ℕ → Prog Bool) (k : Prog Bool),
      leanVmProgram (bytecodeWords prog) (publicDigest input) =
        (Prog.readN (announce s ρ).length).bind (fun a ↦ (f a).bind g) ∧
      g (verifierLayout prog s, ρ) =
        Prog.commit (stackHeight (leanIsaμ prog s) ⟨laneBits, ρ, q₀⟩) (2 ^ laneBits) k :=
    ⟨_, _, by
      rw [length_announce]
      simp only [leanVmProgram, verifyExecution, Prog.bind_eq, hf, Prog.bind_assoc]
      rfl, by
      simp only [commitStack, stackLog_verifierLayout, hc, Verifier.liftOption, Prog.ret_bind,
        Prog.commitP, Prog.bind_eq]
      rfl⟩
  rw [hP] at ht
  obtain ⟨cv, hcv⟩ := proveFrom_readN_bind H S fuel (announce s ρ) _ seed [] hmsg
  rw [hcv, hfa, Prog.ret_bind, hk] at ht
  simp only [proveFrom, hword] at ht
  rw [Option.map_map] at ht
  obtain ⟨t', -, rfl⟩ := Option.map_eq_some_iff.mp ht
  exact ⟨_, rest, t'.1, hc, rfl⟩

/-- **What V_I reads of the deployed honest proof**: the announced layout and rate are the
verifier's at the honest sizes, the stack's root is the root of the honest stack's word, and the
stack's shape is `commitStack`'s. -/
theorem nodeHead_prove_dep (H : Bytes → Digest) {prog : Program} {s : Sizes} {ρ : ℕ}
    {q : Column (leanIsaμ prog s)} {input : PublicInput} (hs : s.Admissible prog)
    (hρ : validRate ρ) {seed : Digest} {fuel : ℕ} {π : Proof}
    (hπ : prove H (leanVmProgram (bytecodeWords prog) (publicDigest input))
      (leanVmProver prog s ρ q) seed fuel = some π) :
    ∃ level rest, deriveConfig (leanIsaμ prog s) ρ = some (level :: rest) ∧
      Verifier.announced (bytecodeWords prog) π.stream = some (verifierLayout prog s, ρ) ∧
      stackRoot π = some (digestScalars (treeRoot H (stackHeight (leanIsaμ prog s) level)
        (stackWord (leanIsaμ prog s) q))) ∧
      stackShape (verifierLayout prog s) ρ = some (levelShape (leanIsaμ prog s) level
        (2 ^ level.fold)) := by
  obtain ⟨level, rest, tail, hc, hst⟩ := prove_stream_head_dep H hs hρ hπ
  refine ⟨level, rest, hc, by rw [hst]; exact announced_announce prog hs hρ _, ?_, ?_⟩
  · have hl := length_announce s ρ
    simp only [stackRoot, hst]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      hl, Nat.sub_self, show 3 + tables.length - (2 + tables.length) = 1 by omega]
    rfl
  · simp only [stackShape, stackLog_verifierLayout, hc]

/-! ## The deferring verifier on the deployed proof -/

/-- **The fixed claims of a run of the deployed verifier**: the bytecode's value at the bus
phase's point, the lincheck's challenge, skip challenge, points and slices, and the matrices'
value the deployed verifier computes there. -/
def freshOfDep (layout : Layout) (t : List E × E × (E × List E × List E) × List E × E × E)
    (zc : ZerocheckResult) (u : E × List E × E × List E) : FixedClaims where
  bytecodePoint := bcPoint layout t
  bytecodeValue := multilinearEval (layout.bytecode.map ofK) (bcPoint layout t)
  alpha := u.1
  zSkip := zc.zSkip
  rowPoint := zc.chi.take flockNumLincheckRounds
  columnPoint := u.2.1.reverse
  slices := u.2.2.2
  matrixValue := blake2sBilinear u.1 (lincheckRowWeights zc.zSkip
    (zc.chi.take flockNumLincheckRounds)) (lincheckColumnWeights u.2.1.reverse u.2.2.2)

/-- **The deployed honest proof is the deferring verifier's**, with true fixed claims read off
its own run, for every hash: the honest prover of the deferring verifier's program gives the same
proof, and the strategy wins its run along the Fiat–Shamir challenges. -/
theorem exists_deferred_dep (H : Bytes → Digest) {prog : Program} {s : Sizes} {ρ : ℕ}
    {q : Column (LeanIsa.leanIsaμ prog s)} {input : PublicInput} (hs : s.Admissible prog)
    (hρ : LeanIsa.validRate ρ) (hq : M3Honest (EndToEnd.Complete.inst prog s) input q)
    {fuel : ℕ} {π : Proof}
    (hπ : prove H (leanVmProgram (bytecodeWords prog) (publicDigest input))
      (leanVmProver prog s ρ q)
      (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) fuel = some π) :
    ∃ c : FixedClaims, c.Holds (bytecodeWords prog) ∧
      prove H (deferredProgram c (bytecodeWords prog) (publicDigest input))
        (leanVmProver prog s ρ q)
        (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) fuel = some π ∧
      ∃ cv' h', fsRun H (leanVmProver prog s ρ q) fuel
        (deferredProgram c (bytecodeWords prog) (publicDigest input))
        (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) [] =
          some (true, cv', h') := by
  set S := leanVmProver prog s ρ q
  set bc := bytecodeWords prog
  set pd := publicDigest input
  set seed := Id.run (seedWith H bc pd)
  have hacc0 : S.AcceptsFrom (leanVmProgram bc pd) [] :=
    Strategy.acceptsFrom_of_runFrom _ []
      (fun chal ↦ (runI_leanVmProgram hs hρ hq walkFaithful_blake2sFlockSpec chal).1)
      (fun chal ↦ (runI_leanVmProgram hs hρ hq walkFaithful_blake2sFlockSpec chal).2)
  have hne : proveFrom H S fuel (leanVmProgram bc pd) seed [] ≠ none := by
    intro h0
    simp [prove, h0] at hπ
  obtain ⟨cvf, hf, hacc⟩ := fsRun_of_acceptsFrom H S fuel _ seed [] hacc0 hne
  have hacc' := hacc
  have hπ' := hπ
  obtain ⟨tπ, htπ, rfl⟩ := Option.map_eq_some_iff.mp hπ'
  simp only [leanVmProgram, verifyExecution, LeanVM.E2E.Complete.verifyBusBalance_eq, verifyFlock,
    LeanVM.E2E.Complete.verifyFlockLincheck_eq, Prog.bind_eq, Prog.bind_assoc, Prog.ret_bind,
    Prog.pure_eq]
    at hacc
  obtain ⟨a, cv1, h1, hp1, hacc⟩ := fsRun_bind_some hacc
  obtain ⟨a1, cv2, h2, hp2, hacc⟩ := fsRun_bind_some hacc
  obtain ⟨t, cv3, h3, hp3, hacc⟩ := fsRun_bind_some hacc
  obtain ⟨v, cv4, h4, hp4, hacc⟩ := fsRun_bind_some hacc
  simp only [Evaluations.computed, Prog.pure_eq, fsRun, Option.some.injEq, Prod.mk.injEq] at hp4
  obtain ⟨rfl, rfl, rfl⟩ := hp4
  obtain ⟨a4, cv5, h5, hp5, hacc⟩ := fsRun_bind_some hacc
  obtain ⟨a5, cv6, h6, hp6, hacc⟩ := fsRun_bind_some hacc
  obtain ⟨zc, cv7, h7, hp7, hacc⟩ := fsRun_bind_some hacc
  obtain ⟨u, cv8, h8, hp8, hacc⟩ := fsRun_bind_some hacc
  have hbc : a.1.bytecode = bc :=
    fsRun_allRet H S fuel (Q := fun r : Layout × ℕ ↦ r.1.bytecode = bc) _ _ _
      (allRet_readSizes bc) hp1
  have hsame : FsSame H S fuel (deferredProgram (freshOfDep a.1 t zc u) bc pd)
      (leanVmProgram bc pd) seed [] := by
    simp only [deferredProgram, leanVmProgram, verifyExecution,
      LeanVM.E2E.Complete.verifyBusBalance_eq, verifyFlock,
      LeanVM.E2E.Complete.verifyFlockLincheck_eq, Prog.bind_eq, Prog.bind_assoc, Prog.ret_bind,
      Prog.pure_eq]
    refine fsSame_bind H S fuel hp1 ?_
    refine fsSame_bind H S fuel hp2 ?_
    refine fsSame_bind H S fuel hp3 ?_
    have e1 : (Evaluations.claimed (freshOfDep a.1 t zc u)).bytecode a.1.bytecode (bcPoint a.1 t) =
        Prog.ret (multilinearEval (a.1.bytecode.map ofK) (bcPoint a.1 t)) := by
      simp [Evaluations.claimed, freshOfDep, Prog.require]
    have e1' : Evaluations.computed.bytecode a.1.bytecode (bcPoint a.1 t) =
        Prog.ret (multilinearEval (a.1.bytecode.map ofK) (bcPoint a.1 t)) := rfl
    rw [e1, e1', Prog.ret_bind, Prog.ret_bind]
    refine fsSame_bind H S fuel hp5 ?_
    refine fsSame_bind H S fuel hp6 ?_
    refine fsSame_bind H S fuel hp7 ?_
    refine fsSame_bind H S fuel hp8 ?_
    have e2 : (Evaluations.claimed (freshOfDep a.1 t zc u)).matrices u.1 zc.zSkip
        (zc.chi.take flockNumLincheckRounds) u.2.1.reverse u.2.2.2 =
        Prog.ret (freshOfDep a.1 t zc u).matrixValue := by
      simp [Evaluations.claimed, freshOfDep, Prog.require]
    have e2' : Evaluations.computed.matrices u.1 zc.zSkip
        (zc.chi.take flockNumLincheckRounds) u.2.1.reverse u.2.2.2 =
        Prog.ret (freshOfDep a.1 t zc u).matrixValue := rfl
    rw [e2, e2']
    exact fsSame_refl H S fuel _ _ _
  have hprove : prove H (deferredProgram (freshOfDep a.1 t zc u) bc pd) S seed fuel =
      some ⟨tπ.1, tπ.2⟩ := by
    simp only [prove, hsame.2, htπ, Option.map_some]
  have hfs : fsRun H S fuel (deferredProgram (freshOfDep a.1 t zc u) bc pd) seed [] =
      some (true, cvf, hf) := hsame.1.trans hacc'
  refine ⟨_, ⟨?_, by simp only [freshOfDep]⟩, hprove, cvf, hf, hfs⟩
  simp only [freshOfDep, hbc]

end
end LeanVM.E2E.SanityDeployed
