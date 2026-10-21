/-
  LeanVM.E2E.Complete.Deferred

  The deferring verifier accepts V°'s honest proof with the fixed polynomials' values read off
  its own run: the bytecode's true value, and the matrices' value that closes the lincheck's
  terminal.
-/

module

public import LeanVM.E2E.Complete.FsRun
public import LeanVM.Protocol.EndToEnd.Blind.Complete

/-!
# The deferring verifier on V°'s proof

A child's proof is checked in circuit by the deferring verifier (`verifyDeferredWith`,
`deferredProgram c`): the deployed verifier with the fixed polynomials' values claimed by `c`
(`Evaluations.claimed c`). It differs from V° (`blindProgram`) at two places:

* the bus phase's bytecode value: `.claimed c` checks the point is `c.bytecodePoint` and returns
  `c.bytecodeValue`, `.computed` returns the bytecode's multilinear extension there;
* the lincheck's end: `.claimed c` checks `alpha`, `zSkip`, the points and the slices are `c`'s
  and returns `c.matrixValue`, then the terminal identity is checked; V° checks nothing.

Both programs are written as the same skeleton with these two holes (`deferredProgram_eq`,
`blindProgram_eq`, the bus split at its bytecode value by `busPre`, `busPost`, the lincheck at
its matrices' value by `linPre`). Along V°'s honest run (`FsRun.lean`) the holes are reached at
one point each; `freshOf` reads `c` off them, the matrices' value being the terminal's solution
`rLc − α²·eq·⟨skip, s⟩ − α³·wCol[const]` (coefficient `1`). Then both checks pass and the holes
return what V°'s do, so the two programs agree along the run (`FsSame`): the honest proof is the
same, and the deferring verifier accepts it (`verifyDeferredWith_honest`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.LeanIsa

@[expose] public section

/-! ## The bus phase, split at the bytecode's value -/

/-- What the bus phase reads before the bytecode's value: the bus challenges, the GKR result,
the memory's three claimed values and the two final counters. -/
def busPre (layout : Layout) : Prog (List E × E × (E × List E × List E) × List E × E × E) := do
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let alphas ← Prog.sampleN busBits
  let beta ← Prog.sampleE
  let g ← verifyGkrGrandProducts pushLayout.depth
  Prog.require (g.1 ≠ 0)
  let memory ← Prog.readN 3
  let memoryFinal ← Prog.readE
  let bytecodeFinal ← Prog.readE
  return (alphas, beta, g, memory, memoryFinal, bytecodeFinal)

/-- The point the bus phase evaluates the bytecode at. -/
def bcPoint (layout : Layout) (t : List E × E × (E × List E × List E) × List E × E × E) : List E :=
  t.2.2.1.2.1.take layout.logBytecode ++ t.1

/-- The bus phase's result from what it read and the bytecode's value. -/
def busPost (layout : Layout) (t : List E × E × (E × List E × List E) × List E × E × E)
    (bytecodeValue : E) : BusResult :=
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let alphas := t.1
  let weights := eqKernel alphas
  let beta := t.2.1
  let point := t.2.2.1.2.1
  let treeValues := t.2.2.1.2.2
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memory := t.2.2.2.1
  let memoryFinal := t.2.2.2.2.1
  let bytecodeFinal := t.2.2.2.2.2
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1, memory2]
      memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let fp := fingerprints weights memory memoryLow bytecodeLow bytecodeValue
  let finalPc := Verifier.gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (Verifier.gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp finalPc memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  ⟨claims, point, forms3, [total0, total1, total2]⟩

/-- **The bus phase, split at the bytecode's value.** -/
theorem verifyBusBalance_eq (ev : Evaluations) (layout : Layout) :
    verifyBusBalance ev layout = (busPre layout).bind fun t ↦
      (ev.bytecode layout.bytecode (bcPoint layout t)).bind fun v ↦ Prog.ret (busPost layout t v) := by
  simp only [verifyBusBalance, busPre, busPost, bcPoint, Prog.bind_eq, Prog.bind_assoc,
    Prog.ret_bind, Prog.pure_eq]

/-! ## The lincheck, split at the matrices' value -/

/-- What the lincheck reads before the matrices' value: its challenge, its sumcheck's point and
final claim, and the slices. -/
def linPre (zc : ZerocheckResult) : Prog (E × List E × E × List E) := do
  let alpha ← Prog.sampleE
  let claim := zc.vA + alpha * zc.vB + alpha ^ 2 * zc.vC + alpha ^ 3
  let x ← sumcheck claim 3 (List.replicate flockNumLincheckRounds none)
  let s ← Prog.readN kBits
  return (alpha, x.1, x.2, s)

/-- The lincheck's terminal value at the matrices' value `mv`. -/
def linTerminal (zc : ZerocheckResult) (u : E × List E × E × List E) (mv : E) : E :=
  mv + u.1 ^ 2 * eqEval (zc.chi.take flockNumLincheckRounds) u.2.1.reverse *
      dot (lagrangeWeights kBits zc.zSkip) u.2.2.2 +
    u.1 ^ 3 * (lincheckColumnWeights u.2.1.reverse u.2.2.2).getD blake2sConstantColumn 0

/-- The lincheck's result. -/
def linOut (zc : ZerocheckResult) (u : E × List E × E × List E) : List E × List E :=
  (u.2.1.reverse ++ zc.chi.drop flockNumLincheckRounds, u.2.2.2)

/-- **The lincheck, split at the matrices' value.** -/
theorem verifyFlockLincheck_eq (ev : Evaluations) (zc : ZerocheckResult) :
    verifyFlockLincheck ev zc = (linPre zc).bind fun u ↦
      (ev.matrices u.1 zc.zSkip (zc.chi.take flockNumLincheckRounds) u.2.1.reverse u.2.2.2).bind
        fun mv ↦ (Prog.require (linTerminal zc u mv = u.2.2.1)).bind fun _ ↦
          Prog.ret (linOut zc u) := by
  simp only [verifyFlockLincheck, linPre, linTerminal, linOut, Prog.bind_eq, Prog.bind_assoc,
    Prog.ret_bind, Prog.pure_eq]
  rfl

/-- **V°'s lincheck** is the same reads, returning at once. -/
theorem verifyFlockLincheckBlind_eq (zc : ZerocheckResult) :
    verifyFlockLincheckBlind zc = (linPre zc).bind fun u ↦ Prog.ret (linOut zc u) := by
  simp only [verifyFlockLincheckBlind, linPre, linOut, Prog.bind_eq, Prog.bind_assoc,
    Prog.ret_bind, Prog.pure_eq]

/-! ## What every return satisfies -/

/-- **Every return of `p` satisfies `Q`**, whatever it reads, samples and opens. -/
def AllRet {α : Type} (Q : α → Prop) : Prog α → Prop
  | .ret a => Q a
  | .fail => True
  | .read k => ∀ x, AllRet Q (k x)
  | .sample k => ∀ c, AllRet Q (k c)
  | .grind _ k => AllRet Q k
  | .commit _ _ k => AllRet Q k
  | .query _ _ k => ∀ r, AllRet Q (k r)

theorem AllRet.bind {α β : Type} {Q' : α → Prop} {Q : β → Prop} {f : α → Prog β}
    (hf : ∀ a, Q' a → AllRet Q (f a)) (p : Prog α) (hp : AllRet Q' p) : AllRet Q (p.bind f) := by
  induction p with
  | ret a => exact hf a hp
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit ht w k ih => exact ih hp
  | query i ps k ih => exact fun r ↦ ih r (hp r)

theorem allRet_true {α : Type} : ∀ p : Prog α, AllRet (fun _ ↦ True) p
  | .ret _ => trivial
  | .fail => trivial
  | .read k => fun x ↦ allRet_true (k x)
  | .sample k => fun c ↦ allRet_true (k c)
  | .grind _ k => allRet_true k
  | .commit _ _ k => allRet_true k
  | .query _ _ k => fun r ↦ allRet_true (k r)

/-- The run's result satisfies what every return does. -/
theorem fsRun_allRet (H : Bytes → Digest) (S : Strategy) (fuel : ℕ) {α : Type} {Q : α → Prop} :
    ∀ (p : Prog α) (cv : Digest) (h : List Ev) {a : α} {cv' : Digest} {h' : List Ev},
      AllRet Q p → fsRun H S fuel p cv h = some (a, cv', h') → Q a
  | .ret b, _, _, a, _, _, hq, hr => by
    simp only [fsRun, Option.some.injEq, Prod.mk.injEq] at hr
    exact hr.1 ▸ hq
  | .fail, _, _, _, _, _, _, hr => by simp [fsRun] at hr
  | .read k, _, _, _, _, _, hq, hr => fsRun_allRet H S fuel (k _) _ _ (hq _) hr
  | .sample k, _, _, _, _, _, hq, hr => fsRun_allRet H S fuel (k _) _ _ (hq _) hr
  | .grind b k, cv, _, _, _, _, hq, hr => by
    simp only [fsRun] at hr
    split at hr
    · simp at hr
    · exact fsRun_allRet H S fuel k _ _ hq hr
  | .commit ht w k, _, _, _, _, _, hq, hr => by
    simp only [fsRun] at hr
    split at hr
    · exact fsRun_allRet H S fuel k _ _ hq hr
    · simp at hr
  | .query i ps k, _, h, _, _, _, hq, hr => by
    simp only [fsRun] at hr
    split at hr
    · simp at hr
    · exact fsRun_allRet H S fuel (k _) _ _ (hq _) hr

/-- A built layout carries its bytecode. -/
theorem buildLayout_bytecode {bc : List K} {m : ℕ} {r : List ℕ} {L : Layout}
    (h : buildLayout bc m r = some L) : L.bytecode = bc := by
  unfold buildLayout at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq] at h
      rw [← h]
    · exact absurd h (by simp)

/-- `readSizes`' layout carries the bytecode it was given. -/
theorem allRet_readSizes (bc : List K) :
    AllRet (fun r : Layout × ℕ ↦ r.1.bytecode = bc) (readSizes bc) := by
  unfold readSizes
  simp only [Prog.bind_eq]
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (show AllRet (fun _ ↦ True) (Prog.require _) from allRet_true _)
  refine AllRet.bind (fun _ _ ↦ ?_) _ (show AllRet (fun _ ↦ True) (Prog.require _) from allRet_true _)
  refine AllRet.bind (Q' := fun L : Layout ↦ L.bytecode = bc) (fun L hL ↦ ?_) _ ?_
  · exact AllRet.bind (fun _ _ ↦ hL) _ (allRet_true _)
  · unfold Verifier.liftOption
    split
    · trivial
    · exact buildLayout_bytecode ‹_›

/-! ## The deferring verifier accepts -/

/-- The run decomposes along `bind`. -/
theorem fsRun_bind_some {H : Bytes → Digest} {S : Strategy} {fuel : ℕ} {α β : Type}
    {p : Prog α} {f : α → Prog β} {cv : Digest} {h : List Ev} {r : β × Digest × List Ev}
    (hh : fsRun H S fuel (p.bind f) cv h = some r) :
    ∃ a cv' h', fsRun H S fuel p cv h = some (a, cv', h') ∧ fsRun H S fuel (f a) cv' h' = some r := by
  rw [fsRun_bind, Option.bind_eq_some_iff] at hh
  obtain ⟨⟨a, cv', h'⟩, h1, h2⟩ := hh
  exact ⟨a, cv', h', h1, h2⟩

/-- **The fixed claims of a run of V°**: the bytecode's true value at the bus phase's point,
the lincheck's challenge, skip challenge, points and slices, and the matrices' value closing
its terminal. -/
def freshOf (layout : Layout) (t : List E × E × (E × List E × List E) × List E × E × E)
    (zc : ZerocheckResult) (u : E × List E × E × List E) : FixedClaims where
  bytecodePoint := bcPoint layout t
  bytecodeValue := multilinearEval (layout.bytecode.map ofK) (bcPoint layout t)
  alpha := u.1
  zSkip := zc.zSkip
  rowPoint := zc.chi.take flockNumLincheckRounds
  columnPoint := u.2.1.reverse
  slices := u.2.2.2
  matrixValue := u.2.2.1 - linTerminal zc u 0

/-- The terminal is the matrices' value plus the terminal at `0`. -/
theorem linTerminal_eq (zc : ZerocheckResult) (u : E × List E × E × List E) (mv : E) :
    linTerminal zc u mv = mv + linTerminal zc u 0 := by
  simp only [linTerminal]
  ring

/-- **V°'s honest proof is the deferring verifier's**, with the fixed claims of its own run, for
every hash: the bytecode's claim is its true value, the honest prover of the deferring verifier's
program gives the same proof, and the strategy wins its run along the Fiat–Shamir challenges. -/
theorem exists_deferred_honest (H : Bytes → Digest) {prog : Program} {s : Sizes} {ρ : ℕ}
    {q : Column (LeanIsa.leanIsaμ prog s)} {input : PublicInput} (hs : s.Admissible prog)
    (hρ : LeanIsa.validRate ρ) (hq : EndToEnd.Blind.M3HonestBlind (EndToEnd.Complete.inst prog s) input q)
    {fuel : ℕ} {π : Proof}
    (hπ : prove H (blindProgram (bytecodeWords prog) (publicDigest input))
      (EndToEnd.Blind.honestStrategyBlind prog s ρ q)
      (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) fuel = some π) :
    ∃ c : FixedClaims,
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
  -- V°'s run, decomposed at the two holes.
  simp only [blindProgram, verifyExecutionBlind, verifyBusBalance_eq, verifyFlockBlind,
    verifyFlockLincheckBlind_eq, Prog.bind_eq, Prog.bind_assoc, Prog.ret_bind, Prog.pure_eq]
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
  exact ⟨_, by simp only [freshOf, hbc], hprove, cvf, hf, hfs⟩

/-- **The deferring verifier accepts V°'s honest proof** with the fixed claims of its own run,
for every hash: the bytecode's claim is its true value. -/
theorem verifyDeferredWith_honest (H : Bytes → Digest) {prog : Program} {s : Sizes} {ρ : ℕ}
    {q : Column (LeanIsa.leanIsaμ prog s)} {input : PublicInput} (hs : s.Admissible prog)
    (hρ : LeanIsa.validRate ρ) (hq : EndToEnd.Blind.M3HonestBlind (EndToEnd.Complete.inst prog s) input q)
    {fuel : ℕ} {π : Proof}
    (hπ : prove H (blindProgram (bytecodeWords prog) (publicDigest input))
      (EndToEnd.Blind.honestStrategyBlind prog s ρ q)
      (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) fuel = some π) :
    ∃ c : FixedClaims,
      multilinearEval ((bytecodeWords prog).map ofK) c.bytecodePoint = c.bytecodeValue ∧
      Id.run (verifyDeferredWith (m := Id) H (bytecodeWords prog)
        (Id.run (fiatShamirIvWith H (bytecodeWords prog))) (publicDigest input) c π) = true := by
  obtain ⟨c, hc, hprove, cv', h', hfs⟩ := exists_deferred_honest H hs hρ hq hπ
  refine ⟨c, hc, ?_⟩
  have hrun := runProof_of_fsRun H _ fuel _ _ hfs hprove
  simp only [verifyDeferredWith]
  exact hrun

end
end LeanVM.E2E.Complete
