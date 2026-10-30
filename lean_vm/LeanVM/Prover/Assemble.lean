/-
  LeanVM.Prover.Assemble

  The statement's honest prover is the specification at the execution's own witness: its script
  makes the moves of the specification's honest script, phase by phase, so its proof is the
  specification's, and the completeness theorems apply to it.
-/

import Statement.Prover.Prove
import LeanVM.Prover.Complete
import LeanVM.Prover.Refine
import LeanVM.Prover.Witness
import LeanVM.Prover.Bus
import LeanVM.Prover.Public
import LeanVM.Prover.Table
import LeanVM.Prover.Keccak
import LeanVM.Prover.Ring
import LeanVM.Prover.Whir
import LeanVM.Prover.Ntt

/-!
# The honest prover is the specification at the execution's witness

* `corr_honestScript`: at a valid execution within the cap and a valid rate, the honest script
  (`LeanVM.Prover.honestScript`) of the execution's witness (`witness?`) makes the moves of the
  specification's honest script `honestProver prog s ρ q (leanVmPhases prog s q)` at the
  witness `skelWitness prog input t.image t.runSkels`, its sizes and its stack: the announcement,
  the stack's commitment (`stackWordFast_eq`), the bus (`corr_busFast`), the table sumcheck
  (`corr_tableFast`, which needs the bus's result true: `BusGood`, from the bus phase's
  simulation), the public input (`corr_pubFast`), the Keccak phase (`corr_keccakPhase`, which
  needs the output lanes' point of the table's height, from the table phase's simulation),
  ring switching (`corr_ringFast`) and the opening (`corr_openingFast`).
* `prove_eq_honestComp`: so the prover with the oracle calls is `Rom.honestComp` of the
  specification's strategy there (`honestComp_ofScript_leanVm`, `runScript_corr`).
* `specOnValid_prove`, `childSpec_prove`: the hypotheses of `completeness_of_spec` and
  `guestChildComplete_of_spec`.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Whir.Complete LeanVM.Guest.Child
open Air.Flat (EnsembleWitness)
open OracleComp

/-! ## Scripts: associativity, results -/

namespace Script

variable {α β γ : Type}

theorem bind_assoc' (p : Script α) (f : α → Script β) (g : β → Script γ) :
    (p.bind f).bind g = p.bind fun a ↦ (f a).bind g := by
  induction p with
  | ret a => rfl
  | send x k ih => simp only [bind, ih]
  | sample k ih => simp only [bind, ih]
  | grind k ih => simp only [bind, ih]
  | commit w k ih => simp only [bind, ih]
  | query k ih => simp only [bind, ih]

theorem AllRet.mono {P Q : α → Prop} (hPQ : ∀ a, P a → Q a) :
    ∀ H : Script α, Script.AllRet P H → Script.AllRet Q H
  | .ret a, h => hPQ a h
  | .send _ k, h => AllRet.mono hPQ k h
  | .sample k, h => fun c ↦ AllRet.mono hPQ (k c) (h c)
  | .grind k, h => AllRet.mono hPQ k h
  | .commit _ k, h => AllRet.mono hPQ k h
  | .query k, h => fun rows ↦ AllRet.mono hPQ (k rows) (h rows)

end Script

/-- A script with no opening. -/
def Script.NoQuery {α : Type} : Script α → Prop
  | .ret _ => True
  | .send _ k => Script.NoQuery k
  | .sample k => ∀ c, Script.NoQuery (k c)
  | .grind k => Script.NoQuery k
  | .commit _ k => Script.NoQuery k
  | .query _ => False

theorem Script.NoQuery.bind {α β : Type} {f : α → Script β} (hk : ∀ a, Script.NoQuery (f a)) :
    ∀ H : Script α, Script.NoQuery H → Script.NoQuery (H.bind f)
  | .ret a, _ => hk a
  | .send _ k, h => Script.NoQuery.bind hk k h
  | .sample k, h => fun c ↦ Script.NoQuery.bind hk (k c) (h c)
  | .grind k, h => Script.NoQuery.bind hk k h
  | .commit _ k, h => Script.NoQuery.bind hk k h
  | .query _, h => h.elim

theorem noQuery_sendList : ∀ xs : List E, Script.NoQuery (Script.sendList xs)
  | [] => trivial
  | _ :: xs => noQuery_sendList xs

theorem noQuery_sampleE_bind {β : Type} {f : E → Script β} (h : ∀ c, Script.NoQuery (f c)) :
    Script.NoQuery (Script.sampleE.bind f) := h

theorem noQuery_sendE_bind {β : Type} (x : E) {f : Unit → Script β}
    (h : Script.NoQuery (f ())) : Script.NoQuery ((Script.sendE x).bind f) := h

theorem noQuery_sampleN : ∀ n : ℕ, Script.NoQuery (Script.sampleN n)
  | 0 => trivial
  | n + 1 => by
    show Script.NoQuery (Script.sampleE.bind fun x ↦
      (Script.sampleN n).bind fun xs ↦ Script.ret (x :: xs))
    exact noQuery_sampleE_bind fun _ ↦ Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_sampleN n)

theorem noQuery_hSumcheck (count : ℕ) (claimOf : List E → E) :
    ∀ (modes : List (Option E)) (pre : List E), Script.NoQuery (hSumcheck count claimOf modes pre)
  | [], _ => trivial
  | _ :: modes, pre => by
    simp only [hSumcheck]
    exact Script.NoQuery.bind (fun _ ↦ noQuery_sampleE_bind fun c ↦
      Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_hSumcheck count claimOf modes (pre ++ [c])))
      _ (noQuery_sendList _)

theorem noQuery_hStep (L₀ L₁ L₂ : List E) (k step : ℕ) (s : GkrState) :
    Script.NoQuery (hStep L₀ L₁ L₂ k step s) := by
  unfold hStep
  refine noQuery_sampleE_bind fun c ↦ Script.NoQuery.bind (fun r ↦ ?_) _ (noQuery_hSumcheck _ _ _ _)
  refine Script.NoQuery.bind (fun _ ↦ ?_) _ (noQuery_sendList _)
  refine Script.NoQuery.bind (fun _ ↦ ?_) _ (noQuery_sendList _)
  refine Script.NoQuery.bind (fun _ ↦ ?_) _ (noQuery_sendList _)
  exact Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_sampleN _)

theorem noQuery_hLayers (L₀ L₁ L₂ : List E) :
    ∀ (n : ℕ) (s : GkrState), Script.NoQuery (hLayers L₀ L₁ L₂ n s)
  | 0, _ => trivial
  | 1, s => by
    simp only [hLayers]
    exact Script.NoQuery.bind (fun _ ↦ noQuery_hLayers L₀ L₁ L₂ 0 _) _ (noQuery_hStep _ _ _ _ _ _)
  | n + 2, s => by
    simp only [hLayers]
    split
    · exact Script.NoQuery.bind (fun _ ↦ noQuery_hLayers L₀ L₁ L₂ (n + 1) _) _
        (noQuery_hStep _ _ _ _ _ _)
    · exact Script.NoQuery.bind (fun _ ↦ noQuery_hLayers L₀ L₁ L₂ n _) _
        (noQuery_hStep _ _ _ _ _ _)

theorem noQuery_hGkr (D : ℕ) (L₀ L₁ L₂ : List E) : Script.NoQuery (hGkr D L₀ L₁ L₂) := by
  unfold hGkr
  refine noQuery_sendE_bind L₀.prod (noQuery_sendE_bind L₂.prod ?_)
  exact Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_hLayers _ _ _ _ _)

theorem noQuery_hBusK3 (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))
    (alphas : List E) (beta : E) (g : E × List E × List E) :
    Script.NoQuery (hBusK3 prog s q alphas beta g) := by
  unfold hBusK3
  refine Script.NoQuery.bind (fun _ ↦ ?_) _ (noQuery_sendList _)
  exact noQuery_sendE_bind (mfVal prog s q g.2.1) (noQuery_sendE_bind (bfVal prog s q g.2.1) trivial)

attribute [local irreducible] Script.NoQuery Script.bind hBusK1 hBusK2 hBusK3 hGkr in
theorem noQuery_hBus (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Script.NoQuery (hBus prog s q) := by
  unfold hBus
  refine Script.NoQuery.bind (fun alphas ↦ ?_) _ (noQuery_sampleN _)
  unfold hBusK1
  refine noQuery_sampleE_bind fun beta ↦ ?_
  unfold hBusK2
  exact Script.NoQuery.bind (fun g ↦ noQuery_hBusK3 prog s q alphas beta g) _ (noQuery_hGkr _ _ _ _)

theorem noQuery_hTable (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))
    (bus : BusResult) : Script.NoQuery (hTable prog s q bus) := by
  unfold hTable
  refine noQuery_sampleE_bind fun xi ↦ ?_
  generalize List.replicate (nRounds s) none = modes
  exact Script.NoQuery.bind (fun _ ↦ Script.NoQuery.bind (fun _ ↦ trivial) _ (noQuery_sendList _))
    _ (noQuery_hSumcheck _ _ _ _)

theorem noQuery_hPub (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Script.NoQuery (hPub prog s q) := by
  unfold hPub
  exact noQuery_sampleE_bind fun _ ↦ trivial

/-- A script with no opening that follows a program returns only results the simulation's
relation relates to some result of the program. -/
theorem follows_allRet {α β : Type} {R : Commits → α → β → Prop} :
    ∀ (H : Script α) (P : Prog β) (cs : Commits), Script.NoQuery H → Follows R H P cs →
      Script.AllRet (fun a ↦ ∃ cs' b, R cs' a b) H := by
  intro H
  induction H with
  | ret a => intro P cs _ h; cases P <;> simp only [Follows] at h; exact ⟨_, _, h⟩
  | send x k ih => intro P cs hn h; cases P <;> simp only [Follows] at h; exact ih _ _ hn h
  | sample k ih =>
    intro P cs hn h; cases P <;> simp only [Follows] at h; exact fun c ↦ ih c _ _ (hn c) (h c)
  | grind k ih => intro P cs hn h; cases P <;> simp only [Follows] at h; exact ih _ _ hn h
  | commit W k ih => intro P cs hn h; cases P <;> simp only [Follows] at h; exact ih _ _ hn h.2
  | query k _ => intro _ _ hn; exact hn.elim

/-- A relation on two scripts, strengthened by a property of every result of the second. -/
theorem Corr.and_allRet {α β : Type} {R : α → β → Prop} {P : β → Prop} :
    ∀ (H₁ : Script α) (H₂ : Script β), Corr R H₁ H₂ → Script.AllRet P H₂ →
      Corr (fun a b ↦ R a b ∧ P b) H₁ H₂
  | .ret _, .ret _, h, hp => ⟨h, hp⟩
  | .send _ k, .send _ k', h, hp => ⟨h.1, Corr.and_allRet k k' h.2 hp⟩
  | .sample k, .sample k', h, hp => fun c ↦ Corr.and_allRet (k c) (k' c) (h c) (hp c)
  | .grind k, .grind k', h, hp => Corr.and_allRet k k' h hp
  | .commit _ k, .commit _ k', h, hp => ⟨h.1, Corr.and_allRet k k' h.2 hp⟩
  | .query k, .query k', h, hp => fun rows ↦ Corr.and_allRet (k rows) (k' rows) (h rows) (hp rows)
  | .ret _, .send _ _, h, _ | .ret _, .sample _, h, _ | .ret _, .grind _, h, _
  | .ret _, .commit _ _, h, _ | .ret _, .query _, h, _ | .send _ _, .ret _, h, _
  | .send _ _, .sample _, h, _ | .send _ _, .grind _, h, _ | .send _ _, .commit _ _, h, _
  | .send _ _, .query _, h, _ | .sample _, .ret _, h, _ | .sample _, .send _ _, h, _
  | .sample _, .grind _, h, _ | .sample _, .commit _ _, h, _ | .sample _, .query _, h, _
  | .grind _, .ret _, h, _ | .grind _, .send _ _, h, _ | .grind _, .sample _, h, _
  | .grind _, .commit _ _, h, _ | .grind _, .query _, h, _ | .commit _ _, .ret _, h, _
  | .commit _ _, .send _ _, h, _ | .commit _ _, .sample _, h, _ | .commit _ _, .grind _, h, _
  | .commit _ _, .query _, h, _ | .query _, .ret _, h, _ | .query _, .send _ _, h, _
  | .query _, .sample _, h, _ | .query _, .grind _, h, _ | .query _, .commit _ _, h, _ => h.elim

/-! ## The honest script makes the specification's moves -/

section Honest

variable {prog : Program} {input : PublicInput} {t : Execution prog}

/-- The output lanes' point of an honest claim list has the `KECCAK` table's height. -/
theorem lanes_point_length {s : Sizes} {q : Column (leanIsaμ prog s)}
    {bc tc pc : List ColumnClaim} (hb : ∀ c ∈ bc, c.column < 6) (hp : ∀ c ∈ pc, c.column < 6)
    (z : Vector E (s.τ 5))
    (ht : tc.filter (fun c ↦ c.column ∈ keccakOutputColumns) = honestLanes prog s q z) :
    ((lanesOf (bc ++ tc ++ pc)).headD default).point.length = s.τ 5 := by
  rw [lanesOf_honest prog s q hb hp z ht]
  simp [honestLanes, List.finRange_succ]

/-- The tables' log-heights of the verifier's layout, the `KECCAK` table's among them. -/
theorem tableLogHeights_verifierLayout (s : Sizes) :
    (verifierLayout prog s).tableLogHeights = tableLogs s := rfl

theorem getD_tableLogs_keccak (s : Sizes) : (tableLogs s).getD opKeccak 0 = s.τ 5 := by
  simp [tableLogs, opKeccak]

attribute [local irreducible] Corr Script.bind Script.NoQuery Script.AllRet hBus hTable hPub
  hKeccakPhase hRing honestOpening busFast tableFast pubFast KeccakGkr.keccakPhaseProve ringFast
  openingFast in
/-- **The honest script makes the specification's moves** at the execution's witness, its
sizes and its stack. -/
theorem corr_honestScript (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 28)
    {ρ : ℕ} (hρ : validRate ρ) {W : Witness} (hW : WitnessSpec prog input t W) :
    Corr (fun _ _ ↦ True) (honestScript W (verifierLayout prog (traceSizes prog input t)) ρ)
      (LeanVM.Protocol.EndToEnd.Complete.honestProver prog (traceSizes prog input t) ρ
        (stackOf prog (traceSizes prog input t) (traceWitness prog input t))
        (leanVmPhases prog (traceSizes prog input t)
          (stackOf prog (traceSizes prog input t) (traceWitness prog input t)))) := by
  obtain ⟨⟨-, hw, hs, hadm, -⟩, -⟩ := childFor_trace hv hcap hρ
  obtain ⟨-, -, hWμ, hWcols, hWstack, hWann⟩ := hW
  generalize traceSizes prog input t = s at hWμ hWcols hWstack hWann hw hs hadm ⊢
  generalize traceWitness prog input t = w at hWcols hWstack hw hs ⊢
  have hq := m3Honest_stackOf hw hs
  generalize stackOf prog s w = q at hWcols hWstack hq ⊢
  have hP := leanVmPhases_honest hadm hq
  have hμ : leanIsaμ prog s ≤ 64 := by have := hadm.2.2.2; unfold maxMu at this; omega
  have hcols : ColsOk prog s q W.cols := hWcols
  unfold honestScript LeanVM.Protocol.EndToEnd.Complete.honestProver honestRun
  simp only [Script.bind_eq, Script.bind_assoc', hWann, hWμ, hWstack,
    Enc.stackWordFast_eq hμ]
  refine Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun _ ↦ ?_
  -- the bus
  have hbusRet : Script.AllRet (fun b : BusResult ↦ BusGood prog s q b ∧ ∀ c ∈ b.claims,
      c.column < 6) (hBus prog s q) :=
    Script.AllRet.mono (fun _ ⟨_, _, ⟨_, h1, h2⟩, h3⟩ ↦ h1 ▸ ⟨h2, h3⟩) _
      (follows_allRet _ _ _ (noQuery_hBus prog s q)
        (follows_retOK _ _ _ (hP.bus []) (retOK_busColumns _)))
  refine Corr.bind (fun bus bus' hb ↦ ?_) _ _ (Corr.and_allRet _ _ (corr_busFast hcols) hbusRet)
  obtain ⟨rfl, hbg, hbcol⟩ := hb
  -- the table sumcheck
  have htabRet : Script.AllRet (fun b : List ColumnClaim ↦ ∃ tc, b = bus.claims ++ tc ∧
      ∃ z : Vector E (s.τ 5), tc.filter (fun c ↦ c.column ∈ keccakOutputColumns) =
        honestLanes prog s q z) (hTable prog s q bus) :=
    Script.AllRet.mono (fun _ ⟨_, _, ⟨_, h1, _, h2⟩⟩ ↦ h1 ▸ h2) _
      (follows_allRet _ _ _ (noQuery_hTable prog s q bus) (hP.table bus hbg []))
  refine Corr.bind (fun cl cl' hc ↦ ?_) _ _ (Corr.and_allRet _ _
    (corr_tableFast W.cols hcols _ (tableLogHeights_verifierLayout s) bus hbg) htabRet)
  obtain ⟨rfl, tc, rfl, z, hz⟩ := hc
  -- the public input
  have hpubRet : Script.AllRet (fun b : List ColumnClaim ↦ ∀ c ∈ b, c.column < 6)
      (hPub prog s q) :=
    Script.AllRet.mono (fun _ ⟨_, _, ⟨_, h1, _⟩, h2⟩ ↦ h1 ▸ h2) _
      (follows_allRet _ _ _ (noQuery_hPub prog s q)
        (follows_retOK _ _ _ (follows_publicInputPhase hq.1 []) (retOK_publicColumns _ _)))
  refine Corr.bind (fun pb pb' hp ↦ ?_) _ _ (Corr.and_allRet _ _ (corr_pubFast hcols) hpubRet)
  obtain ⟨rfl, hpcol⟩ := hp
  -- the Keccak phase
  rw [tableLogHeights_verifierLayout, getD_tableLogs_keccak]
  refine Corr.bind (fun kr kr' hk ↦ ?_) _ _
    (KeccakGkr.corr_keccakPhase prog s q W.cols hcols _ (lanes_point_length hbcol hpcol z hz))
  subst hk
  -- ring switching, then the opening
  refine Corr.bind (fun r rs hr ↦ ?_) _ _ (corr_ringFast kr.2.1 kr.2.2)
  obtain ⟨rfl, -, -⟩ := hr
  have hcl : (RingOut.claim r (verifierLayout prog s) ::
      kr.1.map (ClaimDesc.column (verifierLayout prog s))).map ClaimDesc.denote =
      openingClaims prog s (r.target, fun rPrime ↦ ringWeight r.point rPrime
        (ringCoefficients r.challenges)) kr.1 := by
    simp only [openingClaims, RingOut.claim, ClaimDesc.denote, List.map_cons, List.map_map,
      Function.comp_def]
    rfl
  refine Corr.bind (R := fun _ _ ↦ True) (fun _ _ _ ↦ by unfold Corr; trivial) _ _ ?_
  rw [← hcl]
  exact corr_openingFast hμ ρ q _

end Honest

/-! ## The prover is the specification at the execution's witness -/

section Prove

variable {prog : Program} {input : PublicInput} {t : Execution prog}

/-- The prover's layout is the verifier's, at the execution's sizes. -/
theorem buildLayout_witness (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 28)
    {W : Witness} (hW : WitnessSpec prog input t W) :
    buildLayout (bytecodeWords prog) W.logMem W.rows =
      some (verifierLayout prog (traceSizes prog input t)) := by
  obtain ⟨⟨-, -, -, hadm, -⟩, -⟩ := childFor_trace hv hcap (ρ := 1) ⟨le_rfl, by decide⟩
  rw [hW.logMem, hW.rows]
  have e := buildLayout_eq prog (traceSizes prog input t)
  rw [tableRows] at e
  have hok : LayoutOk (traceSizes prog input t) := ⟨hadm.1, hadm.2.1, hadm.2.2.1⟩
  simp only [e, hok, ↓reduceIte]

/-- **The prover with the oracle calls is the specification** at the execution's witness: on a
valid execution within the cap at a valid rate, `prove callKeccak256 callKeccakF1600` is `Rom.honestComp` of the
specification's honest strategy at `skelWitness`, its sizes and its stack. -/
theorem prove_eq_honestComp (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 28)
    {ρ : ℕ} (hρ : 1 ≤ ρ ∧ ρ ≤ 4) (fuel : ℕ) :
    prove callKeccak256 callKeccakF1600 prog input t ρ fuel =
      Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
        (leanVmProgram (bytecodeWords prog) (publicDigest input))
        (leanVmProver prog (traceSizes prog input t) ρ
          (stackOf prog (traceSizes prog input t) (traceWitness prog input t))) fuel := by
  obtain ⟨W, hW, hspec⟩ := witness?_spec hv hcap
  have hL := buildLayout_witness hv hcap hspec
  have e : prove callKeccak256 callKeccakF1600 prog input t ρ fuel =
      (seedWith callKeccak256 callKeccakF1600 (bytecodeWords prog) (publicDigest input) >>= fun seed ↦
        runScript callKeccak256 callKeccakF1600 (leanVmProgram (bytecodeWords prog) (publicDigest input))
          (honestScript W (verifierLayout prog (traceSizes prog input t)) ρ) seed fuel) := by
    simp only [prove, hW, hρ, and_self, ↓reduceIte, hL]
  rw [e]
  refine Eq.trans ?_ (honestComp_ofScript_leanVm (bytecodeWords prog) (publicDigest input)
    (LeanVM.Protocol.EndToEnd.Complete.honestProver prog (traceSizes prog input t) ρ
      (stackOf prog (traceSizes prog input t) (traceWitness prog input t))
      (leanVmPhases prog (traceSizes prog input t)
        (stackOf prog (traceSizes prog input t) (traceWitness prog input t)))) fuel).symm
  exact congrArg (fun k : KeccakState → OracleComp KeccakCalls Proof ↦
      seedWith callKeccak256 callKeccakF1600 (bytecodeWords prog) (publicDigest input) >>= k)
    (funext fun seed ↦ runScript_corr callKeccak256 callKeccakF1600 fuel _ (corr_honestScript hv hcap hρ hspec) seed)

/-- The statement's honest prover is `prove` with the oracle calls. -/
abbrev oracleProver : HonestProver := LeanVM.prover

/-- **The hypothesis of the completeness theorems**: on valid executions within the cap at a
valid rate, the prover is the specification at a child's witness. -/
theorem specOnValid_prove : SpecOnValid oracleProver ChildFor :=
  fun _ _ _ _ fuel hv hcap hρ ↦ ⟨_, _, childFor_trace hv hcap hρ, prove_eq_honestComp hv hcap hρ fuel⟩

/-- The same, at an honest witness. -/
theorem specOnValid_prove_honest : SpecOnValid oracleProver HonestFor :=
  fun prog input t ρ fuel hv hcap hρ ↦
    let ⟨w, s, h, e⟩ := specOnValid_prove prog input t ρ fuel hv hcap hρ
    ⟨w, s, h.1, e⟩

/-- **Everywhere, the prover is the specification at a child's witness or the empty proof.** -/
theorem childSpec_prove (prog : Program) (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ) :
    ChildSpec oracleProver prog input t ρ fuel := by
  by_cases h : ValidExecution prog input t ∧ t.committedSize ≤ 2 ^ 28 ∧ 1 ≤ ρ ∧ ρ ≤ 4
  · exact .inr (specOnValid_prove prog input t ρ fuel h.1 h.2.1 h.2.2)
  · left
    show prove callKeccak256 callKeccakF1600 prog input t ρ fuel = pure ⟨[], []⟩
    unfold prove
    cases hW : witness? prog input t with
    | none => rfl
    | some W =>
      have hs := (isSome_witness?_iff prog input t).mp (by rw [hW]; rfl)
      have hρ : ¬ (1 ≤ ρ ∧ ρ ≤ 4) := fun hρ ↦ h ⟨hs.1, hs.2, hρ⟩
      simp only [hρ, ↓reduceIte]

end Prove

/-! ## Completeness of the named prover -/

/-- **Completeness for the statement's prover**: the body of `LeanVM.Completeness` for
`prove callKeccak256 callKeccakF1600`. -/
theorem completeness_prove :
    ∀ (prog : Program) (input : PublicInput) (t : Execution prog) (ρ : ℕ),
      ValidExecution prog input t → t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
      Pr{let v ← verifierCompletenessExperiment oracleProver prog input t ρ (2 ^ 25)}[v = false] ≤
        (2 : ENNReal)⁻¹ ^ 256 :=
  completeness_of_spec oracleProver specOnValid_prove_honest


end LeanVM.Prover
