/-
  LeanVM.E2E.Complete.Rom.Fresh

  T6-prob: the honest fresh claims of a node's proof, read off an explicit Fiat–Shamir run of V°'s
  prefix (no classical choice over the hash).
-/

module

public import LeanVM.E2E.Complete.Deferred

/-!
# The fresh claims, explicitly

`freshFor` (`Prover.lean`) chooses the fresh claims classically among those the deferring
verifier accepts, a function of the whole hash. Here they are read off a run: `claimsProg` is the
prefix of V° (`blindProgram`) through the lincheck's reads, returning `freshOf` of what it read
(`Deferred.lean`); `freshRun H S fuel bc pd seed` is its run along the Fiat–Shamir challenges
(`fsRun`), a function of the hash's answers on that run only. `exists_deferred_honest_run`: on
V°'s honest proof it is the claims `exists_deferred_honest` constructs, so the deferring verifier
accepts the same proof with them.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.LeanIsa

@[expose] public section

/-- **V°'s prefix that reads the fixed claims**: the sizes, the stack, the bus phase, the tables,
the public input, the zerocheck and the lincheck's reads, returning the claims they fix. -/
def claimsProg (bc : List K) (pd : Digest) : Prog FixedClaims :=
  (readSizes bc).bind fun a ↦
  (commitStack a.1.stackLog a.2).bind fun _ ↦
  (busPre a.1).bind fun t ↦
  (Evaluations.computed.bytecode a.1.bytecode (bcPoint a.1 t)).bind fun v ↦
  (tablePhase a.1 (busPost a.1 t v)).bind fun _ ↦
  (publicInputPhase a.1 pd).bind fun _ ↦
  (verifyFlockZerocheck (blake2sR1csLogSize + a.1.tableLogHeights.getD opBlake2s 0)).bind fun zc ↦
  (linPre zc).bind fun u ↦
  Prog.ret (freshOf a.1 t zc u)

/-- **The fresh claims of a run**: `claimsProg` along the Fiat–Shamir challenges. -/
noncomputable def freshRun (H : Bytes → Digest) (S : Strategy) (fuel : ℕ) (bc : List K)
    (pd seed : Digest) : Option FixedClaims :=
  (fsRun H S fuel (claimsProg bc pd) seed []).map (·.1)

/-- **V°'s honest proof is the deferring verifier's**, with the claims of `freshRun`. -/
theorem exists_deferred_honest_run (H : Bytes → Digest) {prog : Program} {s : Sizes} {ρ : ℕ}
    {q : Column (LeanIsa.leanIsaμ prog s)} {input : PublicInput} (hs : s.Admissible prog)
    (hρ : LeanIsa.validRate ρ) (hq : EndToEnd.Blind.M3HonestBlind (EndToEnd.Complete.inst prog s) input q)
    {fuel : ℕ} {π : Proof}
    (hπ : prove H (blindProgram (bytecodeWords prog) (publicDigest input))
      (EndToEnd.Blind.honestStrategyBlind prog s ρ q)
      (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) fuel = some π) :
    ∃ c : FixedClaims,
      freshRun H (EndToEnd.Blind.honestStrategyBlind prog s ρ q) fuel (bytecodeWords prog)
        (publicDigest input) (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) =
        some c ∧
      multilinearEval ((bytecodeWords prog).map ofK) c.bytecodePoint = c.bytecodeValue ∧
      prove H (deferredProgram c (bytecodeWords prog) (publicDigest input))
        (EndToEnd.Blind.honestStrategyBlind prog s ρ q)
        (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) fuel = some π ∧
      ∃ cv' h', fsRun H (EndToEnd.Blind.honestStrategyBlind prog s ρ q) fuel
        (deferredProgram c (bytecodeWords prog) (publicDigest input))
        (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) [] = some (true, cv', h') := by
  set S := EndToEnd.Blind.honestStrategyBlind prog s ρ q
  set bc := bytecodeWords prog
  set pd := publicDigest input
  set seed := Id.run (seedWith H bc pd)
  have hacc0 : S.AcceptsFrom (blindProgram bc pd) [] :=
    Strategy.acceptsFrom_of_runFrom _ []
      (fun chal ↦ (EndToEnd.Blind.runI_blindProgram hs hρ hq chal).1)
      (fun chal ↦ (EndToEnd.Blind.runI_blindProgram hs hρ hq chal).2)
  have hne : proveFrom H S fuel (blindProgram bc pd) seed [] ≠ none := by
    intro h0
    simp [prove, h0] at hπ
  obtain ⟨cvf, hf, hacc⟩ := fsRun_of_acceptsFrom H S fuel _ seed [] hacc0 hne
  have hπ' := hπ
  obtain ⟨tπ, htπ, rfl⟩ := Option.map_eq_some_iff.mp hπ'
  simp only [blindProgram, verifyExecutionBlind, verifyBusBalance_eq, verifyFlockBlind,
    verifyFlockLincheckBlind_eq, Prog.bind_eq, Prog.bind_assoc, Prog.ret_bind, Prog.pure_eq]
    at hacc
  obtain ⟨a, cv1, h1, hp1, hacc⟩ := fsRun_bind_some hacc
  obtain ⟨a1, cv2, h2, hp2, hacc⟩ := fsRun_bind_some hacc
  obtain ⟨t, cv3, h3, hp3, hacc⟩ := fsRun_bind_some hacc
  obtain ⟨v, cv4, h4, hp4, hacc⟩ := fsRun_bind_some hacc
  have hp4' := hp4
  simp only [Evaluations.computed, Prog.pure_eq, fsRun, Option.some.injEq, Prod.mk.injEq] at hp4'
  obtain ⟨rfl, rfl, rfl⟩ := hp4'
  obtain ⟨a4, cv5, h5, hp5, hacc⟩ := fsRun_bind_some hacc
  obtain ⟨a5, cv6, h6, hp6, hacc⟩ := fsRun_bind_some hacc
  obtain ⟨zc, cv7, h7, hp7, hacc⟩ := fsRun_bind_some hacc
  obtain ⟨u, cv8, h8, hp8, hacc⟩ := fsRun_bind_some hacc
  have hrun : freshRun H S fuel bc pd seed = some (freshOf a.1 t zc u) := by
    simp only [freshRun, claimsProg, fsRun_bind, hp1, Option.bind_some, hp2, hp3, hp4, hp5, hp6,
      hp7, hp8]
    rfl
  have hbc : a.1.bytecode = bc :=
    fsRun_allRet H S fuel (Q := fun r : Layout × ℕ ↦ r.1.bytecode = bc) _ _ _ (allRet_readSizes bc) hp1
  -- The deferring verifier's program agrees with V°'s along the run.
  have hsame : FsSame H S fuel (deferredProgram (freshOf a.1 t zc u) bc pd) (blindProgram bc pd)
      seed [] := by
    simp only [deferredProgram, blindProgram, verifyExecution, verifyExecutionBlind,
      verifyBusBalance_eq, verifyFlock, verifyFlockBlind, verifyFlockLincheck_eq,
      verifyFlockLincheckBlind_eq, Prog.bind_eq, Prog.bind_assoc, Prog.ret_bind, Prog.pure_eq]
    refine fsSame_bind H S fuel hp1 ?_
    refine fsSame_bind H S fuel hp2 ?_
    refine fsSame_bind H S fuel hp3 ?_
    have e1 : (Evaluations.claimed (freshOf a.1 t zc u)).bytecode a.1.bytecode (bcPoint a.1 t) =
        Prog.ret (multilinearEval (a.1.bytecode.map ofK) (bcPoint a.1 t)) := by
      simp [Evaluations.claimed, freshOf, Prog.require]
    rw [e1, Prog.ret_bind]
    refine fsSame_bind H S fuel hp5 ?_
    refine fsSame_bind H S fuel hp6 ?_
    refine fsSame_bind H S fuel hp7 ?_
    refine fsSame_bind H S fuel hp8 ?_
    refine fsSame_of_eq H S fuel ?_ _ _
    have hterm : linTerminal zc u (u.2.2.1 - linTerminal zc u 0) = u.2.2.1 := by
      rw [linTerminal_eq]
      ring
    simp [Evaluations.claimed, freshOf, Prog.require, hterm]
  -- Hence the same proof, accepted by the deferring verifier.
  have hprove : prove H (deferredProgram (freshOf a.1 t zc u) bc pd) S seed fuel =
      some ⟨tπ.1, tπ.2⟩ := by
    simp only [prove, hsame.2, htπ, Option.map_some]
  have hfs : fsRun H S fuel (deferredProgram (freshOf a.1 t zc u) bc pd) seed [] =
      some (true, cvf, hf) := by
    rw [hsame.1]
    simp only [blindProgram, verifyExecutionBlind, verifyBusBalance_eq, verifyFlockBlind,
      verifyFlockLincheckBlind_eq, Prog.bind_eq, Prog.bind_assoc, Prog.ret_bind, Prog.pure_eq]
    rw [fsRun_bind, hp1, Option.bind_some, fsRun_bind, hp2, Option.bind_some, fsRun_bind, hp3,
      Option.bind_some]
    simp only [Evaluations.computed, Prog.pure_eq, Prog.ret_bind]
    rw [fsRun_bind, hp5, Option.bind_some, fsRun_bind, hp6, Option.bind_some, fsRun_bind, hp7,
      Option.bind_some, fsRun_bind, hp8, Option.bind_some]
    exact hacc
  exact ⟨_, hrun, by simp only [freshOf, hbc], hprove, cvf, hf, hfs⟩

end
end LeanVM.E2E.Complete
