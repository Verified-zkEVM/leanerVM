/-
  LeanerVM.Protocol.Compile.Tables

  The executable verifier's table sumcheck, public input and opening claim are the oracle
  verifiers': each phase's algebra on the wire is the phase's guarded verifier run on the
  transcript the wire decodes to, and the opening's claim is the batch of the pool.
-/

module

public import LeanerVM.Protocol.Compile.Bus
public import LeanerVM.Protocol.Verify

/-!
# The table sumcheck, the public input and the opening claim on the wire

**The table sumcheck** (`TableSumcheck.tableSumcheck`, the table slot of `leanVmPhases`). The
executable reads `ξ`, the cubic rounds without their linear coefficients and the columns' values
(`Verify.TableWire`). `tableTr? I s w` is the transcript the wire decodes to, every round
polynomial rebuilt from its wire and the running claim from the claims of the bus phase's output
`s` batched by `ξ`; `tableWireOf I t` reads the wire back. As for the bus phase
(`LeanerVM.Protocol.Compile.Bus`): `tableStep_eq` (the executable's algebra is the oracle
verifier's run on the decoded transcript), `tableStep_eq_some_iff`, `tableTr?_tableWireOf` (an
accepted transcript is the one its wire decodes to), `tableWireOf_tableTr?` and
`tableStep_tableWireOf`.

**The public input** (`deployedPublicInputPhase`). The wire is the transcript (`pubTr`,
`pubWireOf`), and the executable's algebra is the oracle verifier's run on it (`pubStep_eq`), by
definition: `Verify.pubStep` is the deployed phase's `accepts` and `verdict`, not a separate
transcription. Its fidelity to the deployed verifier is therefore that of the phase's
(`PublicInput.verify_simulated`).

**The opening claim.** The opening phase (`openingPhase`) draws `λ` and asks the stack the pool's
weights and values batched by its powers (`Opening.weight`, `Opening.values`); the compiled
protocol opens the commitment at that weight against that value. The executable's
`Verify.openingClaim` is that pair (`openingClaim_eq`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanIsa CompPoly ProtocolSpec SumcheckRound Verify

@[expose] public section

open RoundPoly (ofList?_toList toList_of_ofList?)

namespace Compile

variable (I : M3Instance)

/-! ## The table sumcheck -/

/-- The table sumcheck's transcript from its parts: `ξ`, the rounds and the columns' values. -/
def tableTrOf (ξ : E) (R : (roundsSpec E 3 I.τmax).FullTranscript)
    (v : Vector E I.tableColumns) : (tableSpec I).FullTranscript :=
  (chalTr ξ ++ₜ R) ++ₜ msgTr v

/-- The transcript of the table sumcheck its wire decodes to, from the bus phase's output `s`:
`ξ`, the rounds rebuilt from the claims batched by `ξ`, the columns' values; `none` when the
wire has another shape. -/
def tableTr? (s : I.Stmt × BusOut I) (w : TableWire) : Option (tableSpec I).FullTranscript :=
  (roundsTr? 3 (fun _ ↦ none) I.τmax 0 (powerBatch (TableSumcheck.claimed I s) w.xi)
    w.rounds).bind fun R ↦
    (RoundPoly.ofList? I.tableColumns w.finals).map (tableTrOf I w.xi R)

/-- The table sumcheck's wire, read off its transcript. -/
def tableWireOf (t : (tableSpec I).FullTranscript) : TableWire :=
  let t₂ := FullTranscript.fst (pSpec₁ := draw E ++ₚ roundsSpec E 3 I.τmax)
    (pSpec₂ := say (Vector E I.tableColumns)) t
  let vals := FullTranscript.snd (pSpec₁ := draw E ++ₚ roundsSpec E 3 I.τmax)
    (pSpec₂ := say (Vector E I.tableColumns)) t
  let xi : E := t₂.fst 0
  ⟨xi, roundsWire 1 I.τmax t₂.snd, Vector.toList (n := I.tableColumns) (vals 0)⟩

/-- The wire of a table sumcheck's transcript in its parts. -/
private theorem tableWireOf_tableTrOf (ξ : E) (R : (roundsSpec E 3 I.τmax).FullTranscript)
    (v : Vector E I.tableColumns) :
    tableWireOf I (tableTrOf I ξ R v) = ⟨ξ, roundsWire 1 I.τmax R, v.toList⟩ := by
  simp only [tableWireOf, tableTrOf, FullTranscript.append_fst, FullTranscript.append_snd,
    chalTr_zero, msgTr_zero]

/-- The plain domain is the oracle verifier's domain of every table round. -/
private theorem domain_eq (x : TableSumcheck.Data I) (k : ℕ) (hk : k < I.τmax) :
    Sumcheck.domain (F := E) (n := I.τmax) Sumcheck.unitWeights x k = eqDomain none := by
  simp [Sumcheck.domain, Sumcheck.unitWeights, hk, eqDomain]

/-- The table sumcheck's run on a transcript in its parts: the rounds from the claims batched by
`ξ`, then the final check on the values. -/
theorem run_tableSumcheck (s : I.Stmt × BusOut I) (ξ : E)
    (R : (roundsSpec E 3 I.τmax).FullTranscript) (v : Vector E I.tableColumns) :
    (TableSumcheck.tableSumcheck I).front.run s (tableTrOf I ξ R v) =
      ((Sumcheck.roundsFront (TableSumcheck.tableSummand I) Sumcheck.unitWeights
          TableSumcheck.nodes).run
          (TableSumcheck.start I s ξ (powerBatch (TableSumcheck.claimed I s) ξ)) R).bind
        fun st ↦ if Sumcheck.finalCheck (TableSumcheck.tableSummand I) st v then
          some (TableSumcheck.tableOut I st v) else none := by
  rw [tableTrOf]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.run_sampleFront]
  simp only [ite_true, Option.bind_some]
  rcases (Sumcheck.roundsFront (TableSumcheck.tableSummand I) Sumcheck.unitWeights
      TableSumcheck.nodes).run
      (TableSumcheck.start I s ξ (powerBatch (TableSumcheck.claimed I s) ξ)) R with _ | st
  · rfl
  · rfl

/-- **The executable verifier's table sumcheck is the oracle verifier's**: its algebra on the
wire is the table sumcheck's guarded verifier run on the transcript the wire decodes to. -/
theorem tableStep_eq (s : I.Stmt × BusOut I) (w : TableWire) :
    tableStep I s w = (tableTr? I s w).bind ((TableSumcheck.tableSumcheck I).front.run s) := by
  simp only [tableStep, tableTr?, Option.bind_eq_bind]
  rcases hR : roundsTr? 3 (fun _ ↦ none) I.τmax 0 (powerBatch (TableSumcheck.claimed I s) w.xi)
      w.rounds with _ | R
  · simp only [Option.bind_none]
    by_cases hlen : w.rounds.length = I.τmax
    · rw [replayRounds_eq_none _ I.τmax 0 _ w.rounds hlen hR]
      rfl
    · rcases hrep : replayRounds 3 (fun _ ↦ none) 0 (powerBatch (TableSumcheck.claimed I s) w.xi)
          w.rounds with _ | ⟨final, cs⟩
      · rfl
      · have hcs : RoundPoly.ofList? I.τmax cs = none := Option.not_isSome_iff_eq_none.mp (by
          rw [isSome_ofList?, length_of_replayRounds hrep]
          exact hlen)
        simp only [Option.bind_some, hcs, Option.bind_none]
  · obtain ⟨final, cs, hrep, v, hv, hrun⟩ := run_roundsTr
      (Sumcheck.roundPoly (TableSumcheck.tableSummand I) Sumcheck.unitWeights TableSumcheck.nodes)
      (Sumcheck.domain Sumcheck.unitWeights) (fun _ ↦ none) I.τmax I.τmax 0 (Nat.zero_add _)
      ((s, w.xi), (#v[], powerBatch (TableSumcheck.claimed I s) w.xi)) w.rounds R
      (fun k _ hk ↦ domain_eq I _ k (by omega)) hR
    have hrun' : (Sumcheck.roundsFront (TableSumcheck.tableSummand I) Sumcheck.unitWeights
        TableSumcheck.nodes).run
        (TableSumcheck.start I s w.xi (powerBatch (TableSumcheck.claimed I s) w.xi))
        R = some ((s, w.xi), (v, final)) := hrun
    have hcs : RoundPoly.ofList? I.τmax cs = some v := by
      rw [← ofList?_toList v, hv]
      rfl
    rw [hrep]
    simp only [Option.bind_some, hcs]
    rcases RoundPoly.ofList? I.tableColumns w.finals with _ | vals
    · rfl
    simp only [Option.bind_some, Option.map_some]
    rw [run_tableSumcheck, hrun', Option.bind_some]

/-- The executable accepts the table sumcheck's wire exactly when the transcript it decodes to
exists and the oracle verifier accepts it, with the oracle verifier's output. -/
theorem tableStep_eq_some_iff (s : I.Stmt × BusOut I) (w : TableWire) (o : I.Stmt × TableOut I) :
    tableStep I s w = some o ↔ ∃ t, tableTr? I s w = some t ∧
      (TableSumcheck.tableSumcheck I).front.check s t = true ∧
        (TableSumcheck.tableSumcheck I).front.out s t = o := by
  rw [tableStep_eq, Option.bind_eq_some_iff]
  exact exists_congr fun t ↦ and_congr_right fun _ ↦ Component.Front.run_eq_some_iff _

/-- A transcript of the table sumcheck the oracle verifier accepts is the one its wire decodes
to. -/
theorem tableTr?_tableWireOf (s : I.Stmt × BusOut I) (t : (tableSpec I).FullTranscript)
    (hc : (TableSumcheck.tableSumcheck I).front.check s t = true) :
    tableTr? I s (tableWireOf I t) = some t := by
  obtain ⟨t₂, vals, rfl⟩ := exists_eq_append (p₁ := draw E ++ₚ roundsSpec E 3 I.τmax)
    (p₂ := say (Vector E I.tableColumns)) t
  obtain ⟨tx, R, rfl⟩ := exists_eq_append (p₁ := draw E) (p₂ := roundsSpec E 3 I.τmax) t₂
  rw [eq_chalTr tx, eq_msgTr vals] at hc ⊢
  change (TableSumcheck.tableSumcheck I).front.check s (tableTrOf I (tx 0) R (vals 0)) = true at hc
  change tableTr? I s (tableWireOf I (tableTrOf I (tx 0) R (vals 0))) =
    some (tableTrOf I (tx 0) R (vals 0))
  have hrun := (TableSumcheck.tableSumcheck I).front.run_of_check hc
  rw [run_tableSumcheck] at hrun
  obtain ⟨st, hR, -⟩ := Option.bind_eq_some_iff.mp hrun
  have hRt := roundsTr?_roundsWire
    (Sumcheck.roundPoly (TableSumcheck.tableSummand I) Sumcheck.unitWeights TableSumcheck.nodes)
    (Sumcheck.domain Sumcheck.unitWeights) (fun _ ↦ none) I.τmax (by norm_num) 1 I.τmax 0
    (Nat.zero_add _) ((s, tx 0), (#v[], powerBatch (TableSumcheck.claimed I s) (tx 0)))
    R (fun k _ hk ↦ domain_eq I _ k (by omega)) (fun _ _ _ ↦ rfl)
    ((Component.Front.run_eq_some_iff _).mp hR).1
  rw [tableWireOf_tableTrOf]
  simp only [tableTr?]
  rw [hRt, Option.bind_some, ofList?_toList, Option.map_some]

/-- The transcript the table sumcheck's wire decodes to carries the wire. -/
theorem tableWireOf_tableTr? {s : I.Stmt × BusOut I} {w : TableWire}
    {t : (tableSpec I).FullTranscript} (h : tableTr? I s w = some t) : tableWireOf I t = w := by
  simp only [tableTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨R, hR, v, hv, rfl⟩ := h
  rcases w with ⟨xi, rounds, finals⟩
  simp only at hR hv
  rw [tableWireOf_tableTrOf, roundsWire_roundsTr? (fun _ ↦ none) 1 I.τmax 0 _ rounds R
    (fun _ _ _ ↦ rfl) hR, toList_of_ofList? hv]

/-- **On a transcript the oracle verifier accepts, the executable accepts its wire** with the
oracle verifier's output. -/
theorem tableStep_tableWireOf (s : I.Stmt × BusOut I) (t : (tableSpec I).FullTranscript)
    (hc : (TableSumcheck.tableSumcheck I).front.check s t = true) :
    tableStep I s (tableWireOf I t) = some ((TableSumcheck.tableSumcheck I).front.out s t) := by
  rw [tableStep_eq, tableTr?_tableWireOf I s t hc, Option.bind_some,
    (TableSumcheck.tableSumcheck I).front.run_of_check hc]

/-! ## The public input -/

/-- The public input's transcript: its wire. -/
def pubTr (w : PubWire) : pubSpec.FullTranscript
  | ⟨0, _⟩ => w.r
  | ⟨1, _⟩ => w.values
  | ⟨k + 2, h⟩ => absurd h (by omega)

/-- The public input's wire, read off its transcript. -/
def pubWireOf (t : pubSpec.FullTranscript) : PubWire := ⟨t 0, t 1⟩

/-- A transcript of the public input is the transcript of its wire. -/
theorem pubTr_pubWireOf (t : pubSpec.FullTranscript) : pubTr (pubWireOf t) = t :=
  funext fun
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k + 2, h⟩ => absurd h (by omega)

/-- **The executable verifier's public input is the oracle verifier's**: its algebra on the wire
is the deployed phase's guarded verifier run on the wire's transcript. It holds by definition:
`Verify.pubStep` is written as the phase's `accepts` and `verdict`. -/
theorem pubStep_eq (s : I.Stmt × TableOut I) (w : PubWire) :
    pubStep I s w = (deployedPublicInputPhase I).front.run s (pubTr w) :=
  rfl

/-! ## The opening claim -/

/-- Batching by powers does not see how its index is spelled. -/
private theorem batch_cast {n n' : ℕ} (h : n = n') {μ : ℕ} (W : Fin n' → Weight E μ) (ρ : E) :
    Weight.batch (fun j : Fin n ↦ W (Fin.cast h j)) ρ = Weight.batch W ρ := by
  subst h
  rfl

/-- Batching values by powers does not see how its index is spelled. -/
private theorem powerBatch_cast {n n' : ℕ} (h : n = n') (a : Fin n' → E) (ρ : E) :
    powerBatch (fun j : Fin n ↦ a (Fin.cast h j)) ρ = powerBatch a ρ := by
  subst h
  rfl

/-- **The executable's opening claim is the opening phase's batch**: the pool's weights and
values batched by the powers of `λ`. -/
theorem openingClaim_eq (s : I.Stmt × FlockOut I) (lam : E) :
    openingClaim I s lam = (Opening.weight I s lam, powerBatch (Opening.values I s) lam) := by
  have hlen : (Opening.poolList I s.2).toArray.size = I.poolSize := by
    rw [List.size_toArray]
    exact Opening.length_poolList I s.2
  unfold openingClaim Opening.weight Opening.values
  refine Prod.ext ?_ ?_
  · rw [← batch_cast hlen]
    simp only [Opening.pool, Fin.val_cast]
    rfl
  · rw [← powerBatch_cast hlen]
    simp only [Opening.pool, Fin.val_cast]
    rfl

end Compile

end
end LeanerVM.Protocol
