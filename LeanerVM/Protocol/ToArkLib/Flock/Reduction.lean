/-
  LeanerVM.Protocol.ToArkLib.Flock.Reduction

  The Flock argument for a batch of Boolean R1CS blocks as one component: the zerocheck with a
  univariate skip, the lincheck and ring switching in sequence, its witness that the verifier
  never reads the oracles, and its completeness. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Flock.RingSwitch

/-!
# The Flock argument

`flock` composes, in this order (Annex C, Protocol C.1, and Annex A): the `nRand` drawn
coordinates of the zerocheck point; `P` on the coset of the skip domain; `z_skip`; the `m`
zerocheck rounds on the within-block coordinates and the `κ` on the batch coordinates; `â, b̂`;
`α`; the `m` lincheck rounds; the slices `s`, checked against the native terminal; the `s' + 1`
ring-switching coefficients and the weighted claim. Its schedule is `flockSchedule`. The
verifier only checks the statement and the transcript (`flockFront`), and an honest prover with
a batch that satisfies its R1CS makes it accept a true weighted claim (`flockComplete`).

Nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

namespace Flock

open CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec SumcheckRound BlockR1CS

@[expose] public section

/-- The schedule of a Flock argument: the point's drawn coordinates, the skip message and
`z_skip`, the zerocheck rounds (within-block, then batch), `â, b̂`, `α`, the lincheck rounds, the
slices, the ring-switching coefficients. -/
abbrev flockSchedule (F : Type) (s m κ nRand s' : ℕ) :=
  draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F ++ₚ roundsSpec F 2 m ++ₚ roundsSpec F 2 κ ++ₚ
    say (Vector F 2) ++ₚ draw F ++ₚ roundsSpec F 2 m ++ₚ say (Vector F (2 ^ s)) ++ₚ draws F (s' + 1)

/-! The instances of the schedule's prefixes, which the argument built one append at a time
meets; instance search does not find them for appended schedules. -/

section Instances

variable (F : Type) [SampleableType F] (s m κ nRand : ℕ)

instance instOracleInterfaceFlockSkip :
    ∀ i, OracleInterface ((draws F nRand ++ₚ say (Vector F (2 ^ s))).Message i) :=
  msgAppend (instOracleInterfaceDraws F nRand) (instOracleInterfaceSay _)

instance instSampleableTypeFlockSkip :
    ∀ i, SampleableType ((draws F nRand ++ₚ say (Vector F (2 ^ s))).Challenge i) :=
  chalAppend (instSampleableTypeDraws F nRand) (instSampleableTypeSay _)

instance instOracleInterfaceFlockZskip :
    ∀ i, OracleInterface ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F).Message i) :=
  msgAppend (instOracleInterfaceFlockSkip F s nRand) (instOracleInterfaceDraw F)

instance instSampleableTypeFlockZskip :
    ∀ i, SampleableType ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F).Challenge i) :=
  chalAppend (instSampleableTypeFlockSkip F s nRand) (instSampleableTypeDraw F)

instance instOracleInterfaceFlockZcLow :
    ∀ i, OracleInterface ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F ++ₚ
      roundsSpec F 2 m).Message i) :=
  msgAppend (instOracleInterfaceFlockZskip F s nRand) (instOracleInterfaceRounds F 2 m)

instance instSampleableTypeFlockZcLow :
    ∀ i, SampleableType ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F ++ₚ
      roundsSpec F 2 m).Challenge i) :=
  chalAppend (instSampleableTypeFlockZskip F s nRand) (instSampleableTypeRounds F 2 m)

instance instOracleInterfaceFlockZcHigh :
    ∀ i, OracleInterface ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F ++ₚ
      roundsSpec F 2 m ++ₚ roundsSpec F 2 κ).Message i) :=
  msgAppend (instOracleInterfaceFlockZcLow F s m nRand) (instOracleInterfaceRounds F 2 κ)

instance instSampleableTypeFlockZcHigh :
    ∀ i, SampleableType ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F ++ₚ
      roundsSpec F 2 m ++ₚ roundsSpec F 2 κ).Challenge i) :=
  chalAppend (instSampleableTypeFlockZcLow F s m nRand) (instSampleableTypeRounds F 2 κ)

instance instOracleInterfaceFlockTerm :
    ∀ i, OracleInterface ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F ++ₚ
      roundsSpec F 2 m ++ₚ roundsSpec F 2 κ ++ₚ say (Vector F 2)).Message i) :=
  msgAppend (instOracleInterfaceFlockZcHigh F s m κ nRand) (instOracleInterfaceSay _)

instance instSampleableTypeFlockTerm :
    ∀ i, SampleableType ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F ++ₚ
      roundsSpec F 2 m ++ₚ roundsSpec F 2 κ ++ₚ say (Vector F 2)).Challenge i) :=
  chalAppend (instSampleableTypeFlockZcHigh F s m κ nRand) (instSampleableTypeSay _)

instance instOracleInterfaceFlockAlpha :
    ∀ i, OracleInterface ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F ++ₚ
      roundsSpec F 2 m ++ₚ roundsSpec F 2 κ ++ₚ say (Vector F 2) ++ₚ draw F).Message i) :=
  msgAppend (instOracleInterfaceFlockTerm F s m κ nRand) (instOracleInterfaceDraw F)

instance instSampleableTypeFlockAlpha :
    ∀ i, SampleableType ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F ++ₚ
      roundsSpec F 2 m ++ₚ roundsSpec F 2 κ ++ₚ say (Vector F 2) ++ₚ draw F).Challenge i) :=
  chalAppend (instSampleableTypeFlockTerm F s m κ nRand) (instSampleableTypeDraw F)

instance instOracleInterfaceFlockLin :
    ∀ i, OracleInterface ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F ++ₚ
      roundsSpec F 2 m ++ₚ roundsSpec F 2 κ ++ₚ say (Vector F 2) ++ₚ draw F ++ₚ
      roundsSpec F 2 m).Message i) :=
  msgAppend (instOracleInterfaceFlockAlpha F s m κ nRand) (instOracleInterfaceRounds F 2 m)

instance instSampleableTypeFlockLin :
    ∀ i, SampleableType ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F ++ₚ
      roundsSpec F 2 m ++ₚ roundsSpec F 2 κ ++ₚ say (Vector F 2) ++ₚ draw F ++ₚ
      roundsSpec F 2 m).Challenge i) :=
  chalAppend (instSampleableTypeFlockAlpha F s m κ nRand) (instSampleableTypeRounds F 2 m)

instance instOracleInterfaceFlockSlices :
    ∀ i, OracleInterface ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F ++ₚ
      roundsSpec F 2 m ++ₚ roundsSpec F 2 κ ++ₚ say (Vector F 2) ++ₚ draw F ++ₚ
      roundsSpec F 2 m ++ₚ say (Vector F (2 ^ s))).Message i) :=
  msgAppend (instOracleInterfaceFlockLin F s m κ nRand) (instOracleInterfaceSay _)

instance instSampleableTypeFlockSlices :
    ∀ i, SampleableType ((draws F nRand ++ₚ say (Vector F (2 ^ s)) ++ₚ draw F ++ₚ
      roundsSpec F 2 m ++ₚ roundsSpec F 2 κ ++ₚ say (Vector F 2) ++ₚ draw F ++ₚ
      roundsSpec F 2 m ++ₚ say (Vector F (2 ^ s))).Challenge i) :=
  chalAppend (instSampleableTypeFlockLin F s m κ nRand) (instSampleableTypeSay _)

instance instOracleInterfaceFlockSchedule (s' : ℕ) :
    ∀ i, OracleInterface ((flockSchedule F s m κ nRand s').Message i) :=
  msgAppend (instOracleInterfaceFlockSlices F s m κ nRand) (instOracleInterfaceDraws F (s' + 1))

instance instSampleableTypeFlockSchedule (s' : ℕ) :
    ∀ i, SampleableType ((flockSchedule F s m κ nRand s').Challenge i) :=
  chalAppend (instSampleableTypeFlockSlices F s m κ nRand) (instSampleableTypeDraws F (s' + 1))

end Instances


variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] (P : Params F)
  {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] {W : Type}
  (C : BlockR1CS F (P.s + P.m))
  (z : (∀ i, O i) → Fin (2 ^ P.s) → CMlPolynomialEval F (P.m + P.κ))
  {S : Type} (side : S → (∀ i, O i) → Prop) (s' : ℕ)
  {K : Type} [CommRing K] (φ : K →+* F) (g : K) {μ : ℕ}
  (lift : Vector F (P.m + P.κ) → Vector F μ) {StmtOut : Type}
  (finish : S → Weight F μ → F → StmtOut)

/-- The Flock argument as one component. -/
def flock : Component.Def S O W StmtOut O W (flockSchedule F P.s P.m P.κ P.nRand s') :=
  (pointDraws P.nRand).append (skipMsg P C z) |>.append (skipDraw P) |>.append
    (zcRoundsLow P C z side) |>.append (zcRoundsHigh P C z side) |>.append (zcEnd P C z) |>.append
    (alphaDraw P) |>.append (linRounds P C z side) |>.append (linEnd P C z) |>.append
    (ringSwitch P s' φ g lift finish)

/-- The point's draws read only the transcript. -/
def pointDrawsFront : (j : ℕ) → Component.Front (pointDraws (S := S) (F := F) (O := O) (W := W) j)
  | 0 => Component.passThroughFront O _
  | j + 1 => (pointDrawsFront j).append (Component.sampleFront O F _ _)

/-- The ring-switching draws read only the transcript. -/
def ringDrawsFront : (p : ℕ) → Component.Front (ringDraws P (S := S) (O := O) (W := W) p)
  | 0 => Component.passThroughFront O _
  | p + 1 => (ringDrawsFront p).append (Component.sampleFront O F _ _)

/-- The Flock verifier checks the statement and the transcript and hands the oracles on: it
never reads them. -/
def flockFront : Component.Front (flock P C z side s' φ g lift finish (W := W)) :=
  (pointDrawsFront P.nRand).append (Component.sendCheckedFront O _ _ _ _) |>.append
    (Component.sampleFront O F _ _) |>.append (roundsFront _ _ _ _ _ _) |>.append
    (roundsFront _ _ _ _ _ _) |>.append (Component.sendCheckedFront O _ _ _ _) |>.append
    (Component.sampleFront O F _ _) |>.append (roundsFront _ _ _ _ _ _) |>.append
    (Component.sendCheckedFront O _ _ _ _) |>.append
    ((ringDrawsFront P s').append (Component.sampleFront O F _ _))

variable [CharP F 2] (col : (∀ i, O i) → CMlPolynomialEval K (P.m + P.κ))
  (stack : (∀ i, O i) → CMlPolynomialEval K μ)

/-- **Completeness of the Flock argument.** From an input relation that gives the side condition
and a batch satisfying its R1CS, at distinct skip nodes and for Boolean tables packed into a
table read off `stack`, the honest prover makes the verifier accept with probability one and
hand on a true weighted claim, which `finish` carries into `relOut`. -/
def flockComplete
    (hnodes : Function.Injective fun j : Fin (2 ^ P.s + 2 ^ P.s) ↦ P.nodes.pts[j])
    (relIn : Set ((S × ∀ i, O i) × W)) (relOut : Set ((StmtOut × ∀ i, O i) × W))
    (hIn : ∀ s o w, ((s, o), w) ∈ relIn → side s o ∧ BatchHolds C P.cpos (z o))
    (hout : ∀ sIn o w (Wt : Weight F μ) T, side sIn o → Wt.pair φ (stack o) = T →
      ((finish sIn Wt T, o), w) ∈ relOut)
    (hcell : ∀ o (u : Fin (2 ^ (P.m + P.κ))),
      φ (col o)[u] = ∑ i : Fin (2 ^ P.s), φ (g ^ i.val) * (z o i)[u])
    (hbool : ∀ o i (u : Fin (2 ^ (P.m + P.κ))), (z o i)[u] = 0 ∨ (z o i)[u] = 1)
    (hread : ∀ o p, eval₂Mle (col o) φ p = eval₂Mle (stack o) φ (lift p)) :
    Component.Complete (flock P C z side s' φ g lift finish (W := W)) relIn relOut :=
  (pointDrawsComplete P C z side relIn (fun s o w h ↦ by
      obtain ⟨hside, hholds⟩ := hIn s o w h
      obtain ⟨herr, hconst⟩ := (batchHolds_iff C P.cpos (z o)).mp hholds
      refine ⟨hside, fun i b ↦ ?_, hconst⟩
      rw [evalMle_eq_sum]
      exact Finset.sum_eq_zero fun u _ ↦ by rw [herr i u, zero_mul])
    P.nRand).append (skipMsgComplete P C z side) |>.append
    (skipDrawComplete P C z side hnodes) |>.append (zcRoundsLowComplete P C z side) |>.append
    (zcRoundsHighComplete P C z side) |>.append (zcEndComplete P C z side) |>.append
    (alphaDrawComplete P C z side) |>.append (linRoundsComplete P C z side) |>.append
    (linEndComplete P C z side) |>.append
    (ringSwitchComplete P z side s' φ g lift col stack finish relOut hout hcell hbool hread)

end

end Flock

end LeanerVM.Protocol
