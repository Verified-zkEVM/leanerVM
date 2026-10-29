/-
  LeanerVM.Protocol.Compile.Bus

  The executable verifier's bus phase is the oracle verifier's: its algebra on the wire is the
  bus phase's guarded verifier run on the transcript the wire decodes to, and a transcript the
  oracle verifier accepts is the one its wire decodes to.
-/

module

public import LeanerVM.Protocol.Compile.Rounds
public import LeanerVM.Protocol.ToArkLib.GrandProductRun
public import LeanerVM.Protocol.Verify.Bus

/-!
# The bus phase on the wire

The executable verifier reads the bus phase as its wire (`Verify.BusWire`): the fingerprint
challenges, the two roots, the first combiner, the grand product's layers, each with the
combiner drawn after it, and the boundary values. Its algebra (`Verify.busStep`) replays them.
The oracle verifier of the phase (`busPhase`, the bus slot of `leanVmPhases`) reads a transcript
of `busSpec I`, every round polynomial whole.

* `busTr? I input w`: the transcript the wire `w` decodes to, every round polynomial rebuilt from
  its wire and the running claim of the oracle verifier; `none` when the wire has another shape;
* `DecodeChain.busWireOf I t` (`LeanerVM.Protocol.Verify.WireOf`): the wire read off a
  transcript, every round polynomial without its constant coefficient, which the grand product's
  rounds drop.

**The bus phase is the oracle verifier's** (`busStep_eq`): the executable's algebra is the
oracle verifier's guarded form run on the decoded transcript,
`busStep I h input w = (busTr? I input w).bind ((busPhase I h).front.run input)`. So the
executable accepts exactly when the decoded transcript exists and the oracle verifier accepts it,
with the same output (`busStep_eq_some_iff`). A transcript the oracle verifier accepts is the one
its wire decodes to (`busTr?_busWireOf`), so on it the executable accepts with the oracle
verifier's output (`busStep_busWireOf`); and the decoded transcript carries its wire
(`busWireOf_busTr?`).

A transcript the oracle verifier rejects need not be the one its wire decodes to: the wire drops a
coefficient of every round polynomial, which the decoding rebuilds from the running claim. It is
when its round polynomials pass their checks against the running claims (`BusSolved`, implied by
the oracle verifier's check, `busSolved_of_check`): then the transcript is the one its wire decodes
to (`busTr?_busWireOf_of_solved`), and the executable's verdict on its wire is the oracle
verifier's on it (`busStep_busWireOf_of_solved`).

The grand product goes layer by layer (`replayGkr_cons`, `replayGkr_replicate`,
`replayGkr_odd`, `replayGkr_gkr`): the executable's layer is the oracle verifier's layer run on
the transcript of the layer's wire (`layerTr?`), and the combiner the wire records after a layer
is the next layer's.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanIsa CompPoly CMlPolynomialEval ProtocolSpec
  SumcheckRound Verify DecodeChain

@[expose] public section

open RoundPoly (ofList?_toList toList_of_ofList?)

namespace Compile

/-! ## Vectors read off lists -/

/-- A list reads as a vector exactly when it has the vector's length. -/
theorem isSome_ofList? {n : ℕ} {l : List E} : (RoundPoly.ofList? n l).isSome ↔ l.length = n := by
  unfold RoundPoly.ofList?
  split <;> simp_all

/-- The list of a vector's entries is its list. -/
theorem ofFn_getElem_eq_toList {n : ℕ} (u : Vector E n) :
    List.ofFn (fun i : Fin n ↦ u[i]) = u.toList := by
  rw [← Vector.toList_ofFn]
  congr 1
  ext j hj
  simp

/-- The rounds the executable replays have one challenge per wire. -/
theorem length_of_replayRounds {d : ℕ} {eq? : ℕ → Option E} :
    ∀ {j : ℕ} {claim : E} {rs : List Round} {final : E} {cs : List E},
      replayRounds d eq? j claim rs = some (final, cs) → cs.length = rs.length
  | _, _, [], _, _, h => by
    simp only [replayRounds, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  | j, claim, r :: rs, final, cs, h => by
    revert h
    simp only [replayRounds, Option.bind_eq_bind, Option.pure_def]
    rcases RoundPoly.decode d claim (eq? j) r.wire with _ | q
    · simp
    simp only [Option.bind_some]
    rcases hrest : replayRounds d eq? (j + 1) (RoundPoly.eval q r.chal) rs with _ | ⟨f', cs'⟩
    · simp
    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq]
    rintro ⟨-, rfl⟩
    simp [length_of_replayRounds hrest]

/-! ## The descendants -/

/-- The descendants' lists read back as the descendants. -/
theorem childTables_ofFn {ρ : ℕ} (ch : Fin 3 → Vector E (2 ^ ρ)) :
    childTables ρ (List.ofFn fun i ↦ (ch i).toList) = some ch := by
  simp only [List.ofFn_succ, List.ofFn_zero, childTables, ofList?_toList, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq]
  funext i
  fin_cases i <;> rfl

/-- Descendants read off lists carry them. -/
theorem ofFn_of_childTables {ρ : ℕ} {cs : List (List E)} {ch : Fin 3 → CMlPolynomialEval E ρ}
    (h : childTables ρ cs = some ch) : List.ofFn (fun i ↦ Vector.toList (ch i)) = cs := by
  match cs, h with
  | [a, b, c], h =>
    revert h
    simp only [childTables, Option.bind_eq_bind, Option.pure_def]
    rcases ha : RoundPoly.ofList? (2 ^ ρ) a with _ | ta
    · simp
    rcases hb : RoundPoly.ofList? (2 ^ ρ) b with _ | tb
    · simp
    rcases hc : RoundPoly.ofList? (2 ^ ρ) c with _ | tc
    · simp
    simp only [Option.bind_some, Option.some.injEq]
    rintro rfl
    simp [List.ofFn_succ, toList_of_ofList? ha, toList_of_ofList? hb, toList_of_ofList? hc]

/-! ## The wire of the grand product -/

/-- A layer's transcript is its combiner, its rounds, its descendants and its combination
challenges. -/
private theorem exists_eq_stepTr {ρ m : ℕ} (t : (stepSpec E 3 ρ m).FullTranscript) :
    ∃ (lam : E) (R : (roundsSpec E (2 ^ ρ) m).FullTranscript) (ch : Fin 3 → Vector E (2 ^ ρ))
      (u : Vector E ρ), t = ((chalTr lam ++ₜ R) ++ₜ msgTr ch) ++ₜ chalsTr ρ fun i ↦ u[i] := by
  obtain ⟨f, hf⟩ := exists_eq_chalsTr ρ t.snd
  refine ⟨t.fst.fst.fst 0, t.fst.fst.snd, t.fst.snd 0, Vector.ofFn f, ?_⟩
  conv_lhs => rw [Gkr.eq_stepTr t]
  rw [hf]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

/-- The wire of a layer's transcript in its parts. -/
private theorem layerWire_mk {ρ m : ℕ} (lam : E) (R : (roundsSpec E (2 ^ ρ) m).FullTranscript)
    (ch : Fin 3 → Vector E (2 ^ ρ)) (u : Vector E ρ) (next : E) :
    layerCombiner (((chalTr lam ++ₜ R) ++ₜ msgTr ch) ++ₜ chalsTr ρ fun i ↦ u[i]) = lam ∧
      layerWire (((chalTr lam ++ₜ R) ++ₜ msgTr ch) ++ₜ chalsTr ρ fun i ↦ u[i]) next =
        ⟨roundsWire 0 m R, List.ofFn fun i ↦ (ch i).toList, u.toList, next⟩ := by
  refine ⟨?_, ?_⟩
  · simp only [layerCombiner, drawOf, FullTranscript.append_fst]
    rfl
  · simp only [layerWire, msgOf, FullTranscript.append_fst, FullTranscript.append_snd,
      drawsList_chalsTr, ofFn_getElem_eq_toList]
    rfl

/-! ## A layer on the wire -/

section Layer

variable {X : Type} {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] (μ : ℕ)
  (leaves : X → (∀ i, O i) → Fin 3 → CMlPolynomialEval E μ)

/-- The transcript of a layer of radix `2 ^ ρ` at depth `m` that its wire decodes to, from the
layer statement `ℓ` and the combiner `lam`: the rounds rebuilt from the combined claim with the
point's equality weights, the descendants and the combination challenges. -/
def layerTr? (ρ m : ℕ) (ℓ : Gkr.LayerStmt X E 3 m) (lam : E) (l : GkrLayer) :
    Option (stepSpec E 3 ρ m).FullTranscript :=
  (roundsTr? (2 ^ ρ) (fun j ↦ ℓ.2.1[j]?) m 0 (powerBatch ℓ.2.2 lam) l.rounds).bind fun R ↦
    (childTables ρ l.children).bind fun ch ↦
      (RoundPoly.ofList? ρ l.combos).map fun u ↦
        ((chalTr lam ++ₜ R) ++ₜ msgTr (M := Fin 3 → Vector E (2 ^ ρ)) ch) ++ₜ
          chalsTr ρ fun i ↦ u[i]

/-- The point's equality weights are the oracle verifier's domains of a layer's rounds. -/
private theorem weights_eq (m : ℕ) (x : Gkr.LayerX X E 3 m) (k : ℕ) (hk : k < m) :
    Gkr.weights 3 m x k = eqDomain (x.1.2.1[k]?) := by
  simp [Gkr.weights, SumcheckRound.normalizedWeights, hk, eqDomain]

/-- A layer's rounds drop their constant coefficients. -/
private theorem dropped_eq (m : ℕ) (ℓ : Gkr.LayerStmt X E 3 m) (k : ℕ) (hk : k < m) :
    RoundPoly.dropped (ℓ.2.1[k]?) = 0 := by
  simp [RoundPoly.dropped, hk]

/-- **The executable's layer is the oracle verifier's**: the grand product's replay of a layer,
from the statement `inp s`, is the oracle verifier's layer run on the transcript the layer's wire
decodes to, and the rest replays from that layer's verdict with the combiner recorded after it. -/
theorem replayGkr_cons (ρ : ℕ) (ρs : List ℕ) (m : ℕ) {S : Type}
    (inp : S → Gkr.LayerStmt X E 3 m) (s : S) (lam : E) (l : GkrLayer) (ls : List GkrLayer) :
    replayGkr (ρ :: ρs) m (inp s) lam (l :: ls) =
      ((layerTr? ρ m (inp s) lam l).bind ((Gkr.layerStepFront 3 μ leaves ρ m inp).run s)).bind
        fun ℓ' ↦ replayGkr ρs (m + ρ) ℓ' l.combiner ls := by
  simp only [replayGkr, layerTr?, Option.bind_eq_bind]
  rcases hR : roundsTr? (2 ^ ρ) (fun j ↦ (inp s).2.1[j]?) m 0 (powerBatch (inp s).2.2 lam)
      l.rounds with _ | R
  · simp only [Option.bind_none]
    by_cases hlen : l.rounds.length = m
    · rw [replayRounds_eq_none _ m 0 _ l.rounds hlen hR]
      rfl
    · rcases hrep : replayRounds (2 ^ ρ) (fun j ↦ (inp s).2.1[j]?) 0 (powerBatch (inp s).2.2 lam)
          l.rounds with _ | ⟨final, cs⟩
      · rfl
      · have hcs : RoundPoly.ofList? m cs = none := Option.not_isSome_iff_eq_none.mp (by
          rw [isSome_ofList?, length_of_replayRounds hrep]
          exact hlen)
        simp only [Option.bind_some, hcs, Option.bind_none]
  · obtain ⟨final, cs, hrep, v, hv, hrun⟩ := run_roundsTr (Gkr.roundPoly 3 μ leaves ρ m)
      (Gkr.weights 3 m) (fun j ↦ (inp s).2.1[j]?) m m 0 (Nat.zero_add m)
      ((inp s, lam), (#v[], powerBatch (inp s).2.2 lam)) l.rounds R
      (fun k _ hk ↦ weights_eq m (inp s, lam) k (by omega)) hR
    have hcs : RoundPoly.ofList? m cs = some v := by
      rw [← ofList?_toList v, hv]
      rfl
    rw [hrep]
    simp only [Option.bind_some, hcs]
    rcases hch : childTables ρ l.children with _ | ch
    · cases RoundPoly.ofList? ρ l.combos <;> rfl
    rcases hu : RoundPoly.ofList? ρ l.combos with _ | u
    · rfl
    simp only [Option.bind_some, Option.map_some]
    rw [Gkr.run_layerStepFront, hrun, Option.bind_some]
    by_cases hc : Gkr.combineCheck 3 ρ m ((inp s, lam), (v, final)) ch = true
    · simp [hc]
    · simp [hc]

/-- The executable's grand product keeps the public data. -/
private theorem replayGkr_fst : ∀ (ρs : List ℕ) (m : ℕ) (ℓ : Gkr.LayerStmt X E 3 m) (lam : E)
    (ls : List GkrLayer) (r : Σ n, Gkr.LayerStmt X E 3 n),
    replayGkr ρs m ℓ lam ls = some r → r.2.1 = ℓ.1
  | [], m, ℓ, lam, [], r, h => by
    simp only [replayGkr, Option.some.injEq] at h
    subst h
    rfl
  | [], _, _, _, _ :: _, _, h => nomatch h
  | _ :: _, _, _, _, [], _, h => nomatch h
  | ρ :: ρs, m, ℓ, lam, l :: ls, r, h => by
    revert h
    simp only [replayGkr, Option.bind_eq_bind]
    rcases replayRounds (2 ^ ρ) (fun j ↦ ℓ.2.1[j]?) 0 (powerBatch ℓ.2.2 lam) l.rounds with
      _ | ⟨final, cs⟩
    · simp
    simp only [Option.bind_some]
    rcases RoundPoly.ofList? m cs with _ | c
    · simp
    rcases RoundPoly.ofList? ρ l.combos with _ | u
    · simp
    rcases childTables ρ l.children with _ | ch
    · simp
    by_cases hc : Gkr.combineCheck 3 ρ m ((ℓ, lam), (c, final)) ch = true
    · simp only [Option.bind_some, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      intro h
      exact replayGkr_fst ρs (m + ρ) _ l.combiner ls r h
    · simp [hc]

/-- A layer's round polynomials pass their checks against the running claims, from the layer
statement `ℓ`'s claims batched by the layer's combiner, with the point's equality weights. -/
def LayerSolved (ρ m : ℕ) (ℓ : Gkr.LayerStmt X E 3 m) (t : (stepSpec E 3 ρ m).FullTranscript) :
    Prop :=
  RoundsSolved (fun j ↦ ℓ.2.1[j]?) m 0 (powerBatch ℓ.2.2 (layerCombiner t)) t.fst.fst.snd

/-- A layer's transcript whose round polynomials pass their checks is the one its wire decodes
to. -/
theorem layerTr?_layerWire_of_solved (ρ m : ℕ) (ℓ : Gkr.LayerStmt X E 3 m)
    (t : (stepSpec E 3 ρ m).FullTranscript) (next : E) (hs : LayerSolved ρ m ℓ t) :
    layerTr? ρ m ℓ (layerCombiner t) (layerWire t next) = some t := by
  obtain ⟨lam, R, ch, u, rfl⟩ := exists_eq_stepTr t
  obtain ⟨hlam, hwire⟩ := layerWire_mk lam R ch u next
  rw [LayerSolved, hlam] at hs
  simp only [FullTranscript.append_fst, FullTranscript.append_snd] at hs
  rw [hlam, hwire]
  simp only [layerTr?]
  rw [roundsTr?_roundsWire_of_solved _ (Nat.two_pow_pos ρ) 0 m 0 _ R
      (fun k _ hk ↦ dropped_eq m ℓ k (by omega)) hs,
    Option.bind_some, childTables_ofFn, Option.bind_some, ofList?_toList, Option.map_some]

/-- A layer's transcript the oracle verifier accepts has round polynomials that pass their
checks. -/
theorem layerSolved_of_check (ρ m : ℕ) {S : Type} (inp : S → Gkr.LayerStmt X E 3 m) (s : S)
    (t : (stepSpec E 3 ρ m).FullTranscript)
    (hc : (Gkr.layerStepFront 3 μ leaves ρ m inp).check s t = true) :
    LayerSolved ρ m (inp s) t := by
  obtain ⟨lam, R, ch, u, rfl⟩ := exists_eq_stepTr t
  have hrun := (Gkr.layerStepFront 3 μ leaves ρ m inp).run_of_check hc
  rw [Gkr.run_layerStepFront] at hrun
  obtain ⟨st, hR, -⟩ := Option.bind_eq_some_iff.mp hrun
  rw [LayerSolved, (layerWire_mk lam R ch u 0).1]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  exact roundsSolved_of_check (Gkr.roundPoly 3 μ leaves ρ m) (Gkr.weights 3 m)
    (fun j ↦ (inp s).2.1[j]?) m m 0 (Nat.zero_add m)
    ((inp s, lam), (#v[], powerBatch (inp s).2.2 lam)) R
    (fun k _ hk ↦ weights_eq m (inp s, lam) k (by omega))
    ((Component.Front.run_eq_some_iff _).mp hR).1

/-- A layer's transcript the oracle verifier accepts is the one its wire decodes to. -/
theorem layerTr?_layerWire (ρ m : ℕ) {S : Type} (inp : S → Gkr.LayerStmt X E 3 m) (s : S)
    (t : (stepSpec E 3 ρ m).FullTranscript) (next : E)
    (hc : (Gkr.layerStepFront 3 μ leaves ρ m inp).check s t = true) :
    layerTr? ρ m (inp s) (layerCombiner t) (layerWire t next) = some t :=
  layerTr?_layerWire_of_solved ρ m (inp s) t next (layerSolved_of_check μ leaves ρ m inp s t hc)

/-- The transcript a layer's wire decodes to carries the wire and its combiner. -/
theorem layerWire_layerTr? {ρ m : ℕ} {ℓ : Gkr.LayerStmt X E 3 m} {lam : E} {l : GkrLayer}
    {t : (stepSpec E 3 ρ m).FullTranscript} (h : layerTr? ρ m ℓ lam l = some t) :
    layerCombiner t = lam ∧ layerWire t l.combiner = l := by
  simp only [layerTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨R, hR, ch, hch, u, hu, rfl⟩ := h
  obtain ⟨hlam, hwire⟩ := layerWire_mk lam R ch u l.combiner
  refine ⟨hlam, hwire.trans ?_⟩
  rcases l with ⟨rounds, children, combos, combiner⟩
  simp only at hR hch hu
  rw [roundsWire_roundsTr? (fun j ↦ ℓ.2.1[j]?) 0 m 0 _ rounds R
      (fun k _ hk ↦ dropped_eq m ℓ k (by omega)) hR,
    ofFn_of_childTables hch, toList_of_ofList? hu]

/-! ## Layers of radix four -/

/-- The transcript of `k` layers of radix four from depth `m` that their wires decode to, from the
layer statement `ℓ` and the combiner `lam`: each layer from the oracle verifier's statement after
the one before, with the combiner drawn after the last. -/
def stepsTr? : (k m : ℕ) → Gkr.LayerStmt X E 3 m → E → List GkrLayer →
    Option ((stepsSpec E 3 k m).FullTranscript × E)
  | 0, _, _, lam, [] => some (nilTr, lam)
  | 0, _, _, _, _ :: _ => none
  | _ + 1, _, _, _, [] => none
  | k + 1, m, ℓ, lam, l :: ls =>
    (layerTr? 2 m ℓ lam l).bind fun t ↦
      (stepsTr? k (m + 2) ((Gkr.layerStepFront 3 μ leaves 2 m id).out ℓ t) l.combiner ls).map
        fun p ↦ (Gkr.stepsCons t p.1, p.2)

/-- The executable's layers of radix four are the oracle verifier's, run on the transcript their
wires decode to. -/
theorem replayGkr_replicate : ∀ (k m : ℕ) (h : m + 2 * k = μ) (ℓ : Gkr.LayerStmt X E 3 m)
    (lam : E) (ls : List GkrLayer),
    replayGkr (List.replicate k 2) m ℓ lam ls =
      (stepsTr? μ leaves k m ℓ lam ls).bind fun p ↦
        ((Gkr.layerStepsFront 3 μ leaves k m h).run ℓ p.1).map (⟨μ, ·⟩)
  | 0, m, h, ℓ, lam, [] => by
    obtain rfl : m = μ := by omega
    rfl
  | 0, m, h, ℓ, lam, _ :: _ => rfl
  | k + 1, m, h, ℓ, lam, [] => rfl
  | k + 1, m, h, ℓ, lam, l :: ls => by
    rw [List.replicate_succ, show ℓ = id ℓ from rfl,
      replayGkr_cons μ leaves 2 (List.replicate k 2) m id ℓ lam l ls]
    simp only [stepsTr?, id]
    rcases layerTr? 2 m ℓ lam l with _ | t
    · rfl
    simp only [Option.bind_some]
    rcases hrun : (Gkr.layerStepFront 3 μ leaves 2 m id).run ℓ t with _ | ℓ'
    · rcases stepsTr? μ leaves k (m + 2) ((Gkr.layerStepFront 3 μ leaves 2 m id).out ℓ t)
          l.combiner ls with _ | p
      · rfl
      · simp only [Option.bind_none, Option.map_some, Option.bind_some]
        rw [Gkr.run_layerStepsFront_succ, hrun]
        rfl
    · obtain ⟨-, hout⟩ := (Component.Front.run_eq_some_iff _).mp hrun
      rw [Option.bind_some, replayGkr_replicate k (m + 2) (by omega) ℓ' l.combiner ls, ← hout]
      rcases stepsTr? μ leaves k (m + 2) ((Gkr.layerStepFront 3 μ leaves 2 m id).out ℓ t)
          l.combiner ls with _ | p
      · rfl
      · simp only [Option.bind_some, Option.map_some]
        rw [Gkr.run_layerStepsFront_succ, hrun, Option.bind_some, ← hout]

/-- The round polynomials of `k` layers of radix four from depth `m` pass their checks, each
layer from the oracle verifier's statement after the one before. -/
def StepsSolved : (k m : ℕ) → Gkr.LayerStmt X E 3 m → (stepsSpec E 3 k m).FullTranscript → Prop
  | 0, _, _, _ => True
  | k + 1, m, ℓ, t =>
    let t₁ :=
      FullTranscript.fst (pSpec₁ := stepSpec E 3 2 m) (pSpec₂ := stepsSpec E 3 k (m + 2)) t
    LayerSolved 2 m ℓ t₁ ∧
      StepsSolved k (m + 2) ((Gkr.layerStepFront 3 μ leaves 2 m id).out ℓ t₁)
        (FullTranscript.snd (pSpec₁ := stepSpec E 3 2 m) (pSpec₂ := stepsSpec E 3 k (m + 2)) t)

/-- Layers pass their checks when the first does and the rest do from its statement. -/
theorem stepsSolved_stepsCons {k m : ℕ} (ℓ : Gkr.LayerStmt X E 3 m)
    (t₁ : (stepSpec E 3 2 m).FullTranscript) (t₂ : (stepsSpec E 3 k (m + 2)).FullTranscript) :
    StepsSolved μ leaves (k + 1) m ℓ (Gkr.stepsCons t₁ t₂) ↔ LayerSolved 2 m ℓ t₁ ∧
      StepsSolved μ leaves k (m + 2) ((Gkr.layerStepFront 3 μ leaves 2 m id).out ℓ t₁) t₂ := by
  simp only [StepsSolved, Gkr.stepsCons, FullTranscript.append_fst, FullTranscript.append_snd]

/-- Transcripts of layers of radix four whose round polynomials pass their checks are the ones
their wires decode to. -/
theorem stepsTr?_stepsWire_of_solved : ∀ (k m : ℕ) (ℓ : Gkr.LayerStmt X E 3 m)
    (t : (stepsSpec E 3 k m).FullTranscript) (last : E),
    StepsSolved μ leaves k m ℓ t →
      stepsTr? μ leaves k m ℓ (stepsWire k m t last).1 (stepsWire k m t last).2 = some (t, last)
  | 0, m, ℓ, t, last, _ => by
    rw [eq_nilTr t]
    rfl
  | k + 1, m, ℓ, t, last, hs => by
    obtain ⟨t₁, t₂, rfl⟩ := Gkr.exists_eq_stepsCons t
    rw [stepsSolved_stepsCons] at hs
    have hw : stepsWire (k + 1) m (Gkr.stepsCons t₁ t₂) last =
        (layerCombiner t₁, layerWire t₁ (stepsWire k (m + 2) t₂ last).1 ::
          (stepsWire k (m + 2) t₂ last).2) := by
      simp only [stepsWire, Gkr.stepsCons, FullTranscript.append_fst, FullTranscript.append_snd]
    rw [hw]
    simp only [stepsTr?]
    rw [layerTr?_layerWire_of_solved 2 m ℓ t₁ _ hs.1, Option.bind_some]
    simp only [layerWire]
    rw [stepsTr?_stepsWire_of_solved k (m + 2) _ t₂ last hs.2, Option.map_some]

/-- Layers of radix four the oracle verifier accepts have round polynomials that pass their
checks. -/
theorem stepsSolved_of_check : ∀ (k m : ℕ) (h : m + 2 * k = μ) (ℓ : Gkr.LayerStmt X E 3 m)
    (t : (stepsSpec E 3 k m).FullTranscript),
    (Gkr.layerStepsFront 3 μ leaves k m h).check ℓ t = true → StepsSolved μ leaves k m ℓ t
  | 0, _, _, _, _, _ => trivial
  | k + 1, m, h, ℓ, t, hc => by
    obtain ⟨t₁, t₂, rfl⟩ := Gkr.exists_eq_stepsCons t
    have hrun := (Gkr.layerStepsFront 3 μ leaves (k + 1) m h).run_of_check hc
    rw [Gkr.run_layerStepsFront_succ] at hrun
    obtain ⟨ℓ', h₁, h₂⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨hc₁, hout⟩ := (Component.Front.run_eq_some_iff _).mp h₁
    rw [stepsSolved_stepsCons, hout]
    exact ⟨layerSolved_of_check μ leaves 2 m id ℓ t₁ hc₁,
      stepsSolved_of_check k (m + 2) (by omega) ℓ' t₂
        ((Component.Front.run_eq_some_iff _).mp h₂).1⟩

/-- Transcripts of layers of radix four the oracle verifier accepts are the ones their wires
decode to. -/
theorem stepsTr?_stepsWire (k m : ℕ) (h : m + 2 * k = μ) (ℓ : Gkr.LayerStmt X E 3 m)
    (t : (stepsSpec E 3 k m).FullTranscript) (last : E)
    (hc : (Gkr.layerStepsFront 3 μ leaves k m h).check ℓ t = true) :
    stepsTr? μ leaves k m ℓ (stepsWire k m t last).1 (stepsWire k m t last).2 = some (t, last) :=
  stepsTr?_stepsWire_of_solved μ leaves k m ℓ t last (stepsSolved_of_check μ leaves k m h ℓ t hc)

/-- The transcript of layers of radix four their wires decode to carries the wires. -/
theorem stepsWire_stepsTr? : ∀ (k m : ℕ) (ℓ : Gkr.LayerStmt X E 3 m) (lam : E)
    (ls : List GkrLayer) (t : (stepsSpec E 3 k m).FullTranscript) (last : E),
    stepsTr? μ leaves k m ℓ lam ls = some (t, last) → stepsWire k m t last = (lam, ls)
  | 0, _, _, lam, [], t, last, h => by
    simp only [stepsTr?, Option.some.injEq] at h
    cases h
    rfl
  | 0, _, _, _, _ :: _, _, _, h => nomatch h
  | _ + 1, _, _, _, [], _, _, h => nomatch h
  | k + 1, m, ℓ, lam, l :: ls, t, last, h => by
    simp only [stepsTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨t₁, h₁, ⟨t₂, last'⟩, h₂, rfl, rfl⟩ := h
    obtain ⟨hlam, hwire⟩ := layerWire_layerTr? h₁
    have ih := stepsWire_stepsTr? k (m + 2) _ l.combiner ls t₂ last' h₂
    simp only [stepsWire, Gkr.stepsCons, FullTranscript.append_fst, FullTranscript.append_snd, ih,
      hlam, hwire]

/-! ## The grand product -/

/-- The transcript of the binary layer its wire decodes to, if there is one, with the combiner
and the layers left. -/
def oddTr? : (r : ℕ) → (X × (Fin 3 → E)) → E → List GkrLayer →
    Option ((oddSpec E 3 r).FullTranscript × E × List GkrLayer)
  | 0, _, lam, ls => some (nilTr, lam, ls)
  | 1, _, _, [] => none
  | 1, s, lam, l :: ls => (layerTr? 1 0 (Gkr.rootStmt 3 s) lam l).map fun t ↦ (t, l.combiner, ls)
  | _ + 2, _, _, _ => none

/-- The executable's binary layer, if there is one, is the oracle verifier's. -/
theorem replayGkr_odd (r : ℕ) (hr : r ≤ 1) (ρs : List ℕ) (s : X × (Fin 3 → E)) (lam : E)
    (ls : List GkrLayer) :
    replayGkr ((if r = 1 then [1] else []) ++ ρs) 0 (Gkr.rootStmt 3 s) lam ls =
      (oddTr? r s lam ls).bind fun p ↦
        ((Gkr.oddFront 3 μ leaves r hr).run s p.1).bind fun ℓ ↦ replayGkr ρs r ℓ p.2.1 p.2.2 := by
  match r, hr, ls with
  | 0, _, ls => rfl
  | 1, _, [] => rfl
  | 1, _, l :: ls =>
    show replayGkr (1 :: ρs) 0 (Gkr.rootStmt 3 s) lam (l :: ls) = _
    rw [replayGkr_cons μ leaves 1 ρs 0 (Gkr.rootStmt 3) s lam l ls]
    simp only [oddTr?]
    rcases layerTr? 1 0 (Gkr.rootStmt 3 s) lam l with _ | t <;> rfl
  | n + 2, h, _ => exact absurd h (by omega)

/-- The binary layer's round polynomials, if there is one, pass their checks, from the roots. -/
def OddSolved : (r : ℕ) → X × (Fin 3 → E) → (oddSpec E 3 r).FullTranscript → Prop
  | 1, s, t => LayerSolved 1 0 (Gkr.rootStmt 3 s) t
  | _, _, _ => True

/-- The binary layer's transcript whose round polynomials pass their checks is the one its wire
decodes to. -/
theorem oddTr?_oddWire_of_solved : ∀ (r : ℕ) (_ : r ≤ 1) (s : X × (Fin 3 → E))
    (t : (oddSpec E 3 r).FullTranscript) (p : E × List GkrLayer),
    OddSolved r s t → oddTr? r s (oddWire r t p).1 (oddWire r t p).2 = some (t, p.1, p.2)
  | 0, _, s, t, p, _ => by
    rw [eq_nilTr t]
    rfl
  | 1, _, s, t, p, hs => by
    simp only [oddWire, oddTr?]
    rw [layerTr?_layerWire_of_solved 1 0 (Gkr.rootStmt 3 s) t p.1 hs]
    rfl
  | n + 2, h, _, _, _, _ => absurd h (by omega)

/-- The binary layer's transcript the oracle verifier accepts has round polynomials that pass
their checks. -/
theorem oddSolved_of_check : ∀ (r : ℕ) (hr : r ≤ 1) (s : X × (Fin 3 → E))
    (t : (oddSpec E 3 r).FullTranscript), (Gkr.oddFront 3 μ leaves r hr).check s t = true →
      OddSolved r s t
  | 0, _, _, _, _ => trivial
  | 1, _, s, t, hc => layerSolved_of_check μ leaves 1 0 (Gkr.rootStmt 3) s t hc
  | n + 2, h, _, _, _ => absurd h (by omega)

/-- The binary layer's transcript the oracle verifier accepts is the one its wire decodes to. -/
theorem oddTr?_oddWire (r : ℕ) (hr : r ≤ 1) (s : X × (Fin 3 → E))
    (t : (oddSpec E 3 r).FullTranscript) (p : E × List GkrLayer)
    (hc : (Gkr.oddFront 3 μ leaves r hr).check s t = true) :
    oddTr? r s (oddWire r t p).1 (oddWire r t p).2 = some (t, p.1, p.2) :=
  oddTr?_oddWire_of_solved r hr s t p (oddSolved_of_check μ leaves r hr s t hc)

/-- The binary layer's transcript its wire decodes to carries the wire. -/
theorem oddWire_oddTr? : ∀ (r : ℕ) (s : X × (Fin 3 → E)) (lam : E) (ls : List GkrLayer)
    (t : (oddSpec E 3 r).FullTranscript) (lam' : E) (ls' : List GkrLayer),
    oddTr? r s lam ls = some (t, lam', ls') → oddWire r t (lam', ls') = (lam, ls)
  | 0, s, lam, ls, t, lam', ls', h => by
    simp only [oddTr?, Option.some.injEq] at h
    cases h
    rfl
  | 1, s, lam, [], t, lam', ls', h => nomatch h
  | 1, s, lam, l :: ls, t, lam', ls', h => by
    revert h
    show (layerTr? 1 0 (Gkr.rootStmt 3 s) lam l).map (fun t ↦ (t, l.combiner, ls)) =
      some (t, lam', ls') → _
    rcases ht' : layerTr? 1 0 (Gkr.rootStmt 3 s) lam l with _ | t'
    · intro h
      nomatch h
    · intro h
      simp only [Option.map_some] at h
      cases h
      obtain ⟨hlam, hwire⟩ := layerWire_layerTr? ht'
      simp only [oddWire, hlam, hwire]
  | n + 2, s, lam, ls, t, lam', ls', h => nomatch h

/-- The transcript of the grand product its wire decodes to, from the roots `s` and the first
combiner `lam`: the binary layer, if there is one, the layers of radix four from the oracle
verifier's statement after it, and the combiner drawn after the last layer. -/
def gkrTr? (s : X × (Fin 3 → E)) (lam : E) (ls : List GkrLayer) :
    Option (gkrSpec E 3 μ).FullTranscript :=
  (oddTr? (μ % 2) s lam ls).bind fun p ↦
    (stepsTr? μ leaves (μ / 2) (μ % 2)
      ((Gkr.oddFront 3 μ leaves (μ % 2) (Nat.le_of_lt_succ (Nat.mod_lt μ two_pos))).out s p.1)
      p.2.1 p.2.2).map fun q ↦ (p.1 ++ₜ q.1) ++ₜ chalTr q.2

/-- **The executable's grand product is the oracle verifier's**, run on the transcript its wire
decodes to: the last statement, at depth `μ`. -/
theorem replayGkr_gkr (s : X × (Fin 3 → E)) (lam : E) (ls : List GkrLayer) :
    replayGkr (gkrRadices μ) 0 (Gkr.rootStmt 3 s) lam ls =
      (gkrTr? μ leaves s lam ls).bind fun t ↦ ((gkrFront 3 μ leaves).run s t).map (⟨μ, ·⟩) := by
  rw [gkrRadices, replayGkr_odd μ leaves (μ % 2) (Nat.le_of_lt_succ (Nat.mod_lt μ two_pos))]
  simp only [gkrTr?]
  rcases oddTr? (μ % 2) s lam ls with _ | ⟨t₁, lam₁, ls₁⟩
  · rfl
  simp only [Option.bind_some]
  rcases hodd : (Gkr.oddFront 3 μ leaves (μ % 2) _).run s t₁ with _ | ℓ
  · rcases stepsTr? μ leaves (μ / 2) (μ % 2) ((Gkr.oddFront 3 μ leaves (μ % 2) _).out s t₁) lam₁
        ls₁ with _ | ⟨t₂, last⟩
    · rfl
    · simp only [Option.bind_none, Option.map_some, Option.bind_some]
      rw [Gkr.run_gkrFront, hodd]
      rfl
  · obtain ⟨-, hout⟩ := (Component.Front.run_eq_some_iff _).mp hodd
    rw [Option.bind_some, replayGkr_replicate μ leaves (μ / 2) (μ % 2) (Nat.mod_add_div μ 2) ℓ lam₁
      ls₁, ← hout]
    rcases stepsTr? μ leaves (μ / 2) (μ % 2) ((Gkr.oddFront 3 μ leaves (μ % 2) _).out s t₁) lam₁
        ls₁ with _ | ⟨t₂, last⟩
    · rfl
    · simp only [Option.bind_some, Option.map_some]
      rw [Gkr.run_gkrFront, hodd, Option.bind_some, ← hout]

/-- The grand product's round polynomials pass their checks: the binary layer's from the roots
`s`, and the layers of radix four's from the oracle verifier's statement after it. -/
def GkrSolved (s : X × (Fin 3 → E)) (t : (gkrSpec E 3 μ).FullTranscript) : Prop :=
  let t₁₂ := FullTranscript.fst (pSpec₁ := oddSpec E 3 (μ % 2) ++ₚ stepsSpec E 3 (μ / 2) (μ % 2))
    (pSpec₂ := draw E) t
  let t₁ := FullTranscript.fst (pSpec₁ := oddSpec E 3 (μ % 2))
    (pSpec₂ := stepsSpec E 3 (μ / 2) (μ % 2)) t₁₂
  OddSolved (μ % 2) s t₁ ∧
    StepsSolved μ leaves (μ / 2) (μ % 2)
      ((Gkr.oddFront 3 μ leaves (μ % 2) (Nat.le_of_lt_succ (Nat.mod_lt μ two_pos))).out s t₁)
      (FullTranscript.snd (pSpec₁ := oddSpec E 3 (μ % 2))
        (pSpec₂ := stepsSpec E 3 (μ / 2) (μ % 2)) t₁₂)

/-- A transcript of the grand product whose round polynomials pass their checks is the one its
wire decodes to. -/
theorem gkrTr?_gkrWire_of_solved (s : X × (Fin 3 → E)) (t : (gkrSpec E 3 μ).FullTranscript)
    (hs : GkrSolved μ leaves s t) :
    gkrTr? μ leaves s (gkrWire μ t).1 (gkrWire μ t).2 = some t := by
  obtain ⟨t₁₂, tc, rfl⟩ := exists_eq_append
    (p₁ := oddSpec E 3 (μ % 2) ++ₚ stepsSpec E 3 (μ / 2) (μ % 2)) (p₂ := draw E) t
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_append
    (p₁ := oddSpec E 3 (μ % 2)) (p₂ := stepsSpec E 3 (μ / 2) (μ % 2)) t₁₂
  simp only [GkrSolved, FullTranscript.append_fst, FullTranscript.append_snd] at hs
  rw [eq_chalTr tc]
  have hw : gkrWire μ ((t₁ ++ₜ t₂) ++ₜ chalTr (tc 0)) =
      oddWire (μ % 2) t₁ (stepsWire (μ / 2) (μ % 2) t₂ (tc 0)) := by
    simp only [gkrWire, FullTranscript.append_fst, FullTranscript.append_snd, chalTr_zero]
  rw [hw]
  simp only [gkrTr?]
  rw [oddTr?_oddWire_of_solved (μ % 2) (Nat.le_of_lt_succ (Nat.mod_lt μ two_pos)) s t₁ _ hs.1,
    Option.bind_some]
  simp only
  rw [stepsTr?_stepsWire_of_solved μ leaves (μ / 2) (μ % 2) _ t₂ _ hs.2, Option.map_some]

/-- A transcript of the grand product the oracle verifier accepts has round polynomials that pass
their checks. -/
theorem gkrSolved_of_check (s : X × (Fin 3 → E)) (t : (gkrSpec E 3 μ).FullTranscript)
    (hc : (gkrFront 3 μ leaves).check s t = true) : GkrSolved μ leaves s t := by
  obtain ⟨t₁₂, tc, rfl⟩ := exists_eq_append
    (p₁ := oddSpec E 3 (μ % 2) ++ₚ stepsSpec E 3 (μ / 2) (μ % 2)) (p₂ := draw E) t
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_append
    (p₁ := oddSpec E 3 (μ % 2)) (p₂ := stepsSpec E 3 (μ / 2) (μ % 2)) t₁₂
  rw [eq_chalTr tc] at hc
  have hrun := (gkrFront 3 μ leaves).run_of_check hc
  rw [Gkr.run_gkrFront] at hrun
  obtain ⟨ℓ₀, h₀, h₂⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨hc₀, hout⟩ := (Component.Front.run_eq_some_iff _).mp h₀
  simp only [GkrSolved, FullTranscript.append_fst, FullTranscript.append_snd]
  rw [hout]
  exact ⟨oddSolved_of_check μ leaves _ _ s t₁ hc₀,
    stepsSolved_of_check μ leaves _ _ (Nat.mod_add_div μ 2) ℓ₀ t₂
      ((Component.Front.run_eq_some_iff _).mp h₂).1⟩

/-- A transcript of the grand product the oracle verifier accepts is the one its wire decodes
to. -/
theorem gkrTr?_gkrWire (s : X × (Fin 3 → E)) (t : (gkrSpec E 3 μ).FullTranscript)
    (hc : (gkrFront 3 μ leaves).check s t = true) :
    gkrTr? μ leaves s (gkrWire μ t).1 (gkrWire μ t).2 = some t :=
  gkrTr?_gkrWire_of_solved μ leaves s t (gkrSolved_of_check μ leaves s t hc)

/-- The transcript of the grand product its wire decodes to carries the wire. -/
theorem gkrWire_gkrTr? {s : X × (Fin 3 → E)} {lam : E} {ls : List GkrLayer}
    {t : (gkrSpec E 3 μ).FullTranscript} (h : gkrTr? μ leaves s lam ls = some t) :
    gkrWire μ t = (lam, ls) := by
  simp only [gkrTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨t₁, lam₁, ls₁⟩, h₁, ⟨t₂, last⟩, h₂, rfl⟩ := h
  simp only [gkrWire, FullTranscript.append_fst, FullTranscript.append_snd, chalTr_zero]
  rw [stepsWire_stepsTr? μ leaves _ _ _ _ _ t₂ last h₂]
  exact oddWire_oddTr? _ s lam ls t₁ lam₁ ls₁ h₁

end Layer

/-! ## The bus phase -/

variable (I : M3Instance)

/-- The bus phase's transcript from its parts: the fingerprint challenges, the roots, the grand
product and the boundary values. -/
def busTrOf (ab : (Fin 4 → E) × E) (r : E × E) (g : (gkrSpec E 3 I.μBus).FullTranscript)
    (vals : Vector E I.busClaims) : (busSpec I).FullTranscript :=
  ((chalTr ab ++ₜ msgTr r) ++ₜ g) ++ₜ msgTr vals

/-- The transcript of the bus phase its wire decodes to, from the statement `input`: the
fingerprint challenges, the roots, the grand product from the roots, and the boundary values;
`none` when the wire has another shape. -/
def busTr? (input : I.Stmt) (w : BusWire) : Option (busSpec I).FullTranscript :=
  (RoundPoly.ofList? 4 w.alpha).bind fun α ↦
    (gkrTr? I.μBus (Bus.leaves I) ((input, (fun i ↦ α[i], w.beta)), ![w.shared, w.shared, w.count])
      w.combiner w.layers).bind fun g ↦
      (RoundPoly.ofList? I.busClaims w.values).map fun vals ↦
        busTrOf I (fun i ↦ α[i], w.beta) (w.shared, w.count) g vals

/-- The wire of a bus phase's transcript in its parts. -/
private theorem busWireOf_busTrOf (ab : (Fin 4 → E) × E) (r : E × E)
    (g : (gkrSpec E 3 I.μBus).FullTranscript) (vals : Vector E I.busClaims) :
    busWireOf I (busTrOf I ab r g vals) =
      ⟨List.ofFn ab.1, ab.2, r.1, r.2, (gkrWire I.μBus g).1, (gkrWire I.μBus g).2,
        vals.toList⟩ := by
  simp only [busWireOf, busTrOf, drawOf, msgOf, FullTranscript.append_fst,
    FullTranscript.append_snd, chalTr_zero, msgTr_zero]

/-- The bus phase's run on a transcript in its parts: the count root checked, the grand product
from the roots, and the output from its last statement and the values. -/
theorem run_busPhase (h : Bus.Conditions I) (input : I.Stmt) (ab : (Fin 4 → E) × E) (r : E × E)
    (g : (gkrSpec E 3 I.μBus).FullTranscript) (vals : Vector E I.busClaims) :
    (busPhase I h).front.run input (busTrOf I ab r g vals) =
      if r.2 = 0 then none else
        ((gkrFront 3 I.μBus (Bus.leaves I)).run ((input, ab), ![r.1, r.1, r.2]) g).map
          fun ℓ ↦ (ℓ.1.1, Bus.busOut h ℓ vals) := by
  rw [busTrOf]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.Front.run_append]
  simp only [FullTranscript.append_fst, FullTranscript.append_snd]
  erw [Component.run_sampleFront]
  simp only [ite_true, Option.bind_some]
  erw [Component.run_sendCheckedFront]
  by_cases hr : r.2 = 0
  · simp [hr]
  · simp only [hr, ne_eq, not_false_eq_true, decide_true, ite_true, ite_false, Option.bind_some]
    rcases (gkrFront 3 I.μBus (Bus.leaves I)).run ((input, ab), ![r.1, r.1, r.2]) g with _ | ℓ
    · rfl
    · simp only [Option.bind_some, Option.map_some]
      erw [Component.run_sendCheckedFront]
      rfl

/-- **The executable verifier's bus phase is the oracle verifier's**: its algebra on the wire is
the bus phase's guarded verifier run on the transcript the wire decodes to. -/
theorem busStep_eq (h : Bus.Conditions I) (input : I.Stmt) (w : BusWire) :
    busStep I h input w = (busTr? I input w).bind ((busPhase I h).front.run input) := by
  simp only [busStep, busReplay, busTr?, Option.bind_eq_bind, Option.pure_def]
  rcases RoundPoly.ofList? 4 w.alpha with _ | α
  · rfl
  simp only [Option.bind_some]
  have key := replayGkr_gkr I.μBus (Bus.leaves I)
    (((input, ((fun i : Fin 4 ↦ α[i]), w.beta)) : Bus.Data I), ![w.shared, w.shared, w.count])
    w.combiner w.layers
  have hfst := replayGkr_fst (gkrRadices I.μBus) 0
    (Gkr.rootStmt 3 (((input, ((fun i : Fin 4 ↦ α[i]), w.beta)) : Bus.Data I),
      ![w.shared, w.shared, w.count])) w.combiner w.layers
  change replayGkr (gkrRadices I.μBus) 0
    ((((input, ((fun i : Fin 4 ↦ α[i]), w.beta)) : Bus.Data I),
      (#v[], ![w.shared, w.shared, w.count])) : Gkr.LayerStmt (Bus.Data I) E 3 0)
    w.combiner w.layers = _ at key
  rw [key]
  rcases hg : gkrTr? I.μBus (Bus.leaves I) ((input, (fun i ↦ α[i], w.beta)),
      ![w.shared, w.shared, w.count]) w.combiner w.layers with _ | g
  · by_cases hc : w.count = 0 <;> simp [hc]
  rw [hg, Option.bind_some] at key
  simp only [Option.bind_some]
  rcases hv : RoundPoly.ofList? I.busClaims w.values with _ | vals
  · by_cases hc : w.count = 0
    · simp [hc]
    · rcases (gkrFront 3 I.μBus (Bus.leaves I)).run ((input, (fun i ↦ α[i], w.beta)),
          ![w.shared, w.shared, w.count]) g with _ | ℓ
      · simp [hc]
      · simp [hc]
  simp only [Option.map_some, Option.bind_some]
  rw [run_busPhase]
  by_cases hc : w.count = 0
  · simp [hc]
  rcases hrun : (gkrFront 3 I.μBus (Bus.leaves I)).run ((input, (fun i ↦ α[i], w.beta)),
      ![w.shared, w.shared, w.count]) g with _ | ℓ
  · simp [hc]
  · rw [hrun, Option.map_some] at key
    have hin : ℓ.1.1 = input := congrArg Prod.fst (hfst _ key)
    simp only [hc, ↓reduceIte, Option.bind_some, Option.map_some, dite_true, hin]

/-- The executable accepts the bus phase's wire exactly when the transcript it decodes to exists
and the oracle verifier accepts it, with the oracle verifier's output. -/
theorem busStep_eq_some_iff (h : Bus.Conditions I) (input : I.Stmt) (w : BusWire)
    (o : I.Stmt × BusOut I) :
    busStep I h input w = some o ↔ ∃ t, busTr? I input w = some t ∧
      (busPhase I h).front.check input t = true ∧ (busPhase I h).front.out input t = o := by
  rw [busStep_eq, Option.bind_eq_some_iff]
  exact exists_congr fun t ↦ and_congr_right fun _ ↦ Component.Front.run_eq_some_iff _

/-- The bus phase's round polynomials pass their checks: the grand product's, from the roots. -/
def BusSolved (input : I.Stmt) (t : (busSpec I).FullTranscript) : Prop :=
  ∃ ab r g vals, t = busTrOf I ab r g vals ∧
    GkrSolved I.μBus (Bus.leaves I) ((input, ab), ![r.1, r.1, r.2]) g

/-- A transcript of the bus phase whose round polynomials pass their checks is the one its wire
decodes to. -/
theorem busTr?_busWireOf_of_solved (input : I.Stmt) (t : (busSpec I).FullTranscript)
    (hs : BusSolved I input t) : busTr? I input (busWireOf I t) = some t := by
  obtain ⟨ab, r, g, vals, rfl, hg⟩ := hs
  rw [busWireOf_busTrOf]
  simp only [busTr?]
  rw [show List.ofFn ab.1 = (Vector.ofFn ab.1).toList from (Vector.toList_ofFn).symm,
    ofList?_toList, Option.bind_some]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Prod.mk.eta]
  rw [gkrTr?_gkrWire_of_solved I.μBus (Bus.leaves I) _ g hg, Option.bind_some, ofList?_toList,
    Option.map_some]

/-- A transcript of the bus phase the oracle verifier accepts has round polynomials that pass their
checks. -/
theorem busSolved_of_check (h : Bus.Conditions I) (input : I.Stmt)
    (t : (busSpec I).FullTranscript) (hc : (busPhase I h).front.check input t = true) :
    BusSolved I input t := by
  obtain ⟨t₃, vals, rfl⟩ := exists_eq_append
    (p₁ := draw ((Fin 4 → E) × E) ++ₚ say (E × E) ++ₚ gkrSpec E 3 I.μBus)
    (p₂ := say (Vector E I.busClaims)) t
  obtain ⟨t₂, g, rfl⟩ := exists_eq_append
    (p₁ := draw ((Fin 4 → E) × E) ++ₚ say (E × E)) (p₂ := gkrSpec E 3 I.μBus) t₃
  obtain ⟨tab, tr, rfl⟩ := exists_eq_append
    (p₁ := draw ((Fin 4 → E) × E)) (p₂ := say (E × E)) t₂
  rw [eq_chalTr tab, eq_msgTr tr, eq_msgTr vals] at hc ⊢
  change (busPhase I h).front.check input (busTrOf I (tab 0) (tr 0) g (vals 0)) = true at hc
  have hrun := (busPhase I h).front.run_of_check hc
  rw [run_busPhase] at hrun
  split at hrun
  · exact absurd hrun (by simp)
  obtain ⟨ℓ, hg, -⟩ := Option.map_eq_some_iff.mp hrun
  exact ⟨tab 0, tr 0, g, vals 0, rfl, gkrSolved_of_check I.μBus (Bus.leaves I) _ g
    ((Component.Front.run_eq_some_iff _).mp hg).1⟩

/-- A transcript of the bus phase the oracle verifier accepts is the one its wire decodes to. -/
theorem busTr?_busWireOf (h : Bus.Conditions I) (input : I.Stmt) (t : (busSpec I).FullTranscript)
    (hc : (busPhase I h).front.check input t = true) :
    busTr? I input (busWireOf I t) = some t :=
  busTr?_busWireOf_of_solved I input t (busSolved_of_check I h input t hc)

/-- The transcript the bus phase's wire decodes to carries the wire. -/
theorem busWireOf_busTr? {input : I.Stmt} {w : BusWire} {t : (busSpec I).FullTranscript}
    (h : busTr? I input w = some t) : busWireOf I t = w := by
  simp only [busTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨α, hα, g, hg, vals, hv, rfl⟩ := h
  rcases w with ⟨alpha, beta, shared, count, combiner, layers, values⟩
  simp only at hα hg hv
  rw [busWireOf_busTrOf, gkrWire_gkrTr? I.μBus (Bus.leaves I) hg]
  simp only
  rw [ofFn_getElem_eq_toList, toList_of_ofList? hα, toList_of_ofList? hv]

/-- **On a transcript the oracle verifier accepts, the executable accepts its wire** with the
oracle verifier's output. -/
theorem busStep_busWireOf (h : Bus.Conditions I) (input : I.Stmt) (t : (busSpec I).FullTranscript)
    (hc : (busPhase I h).front.check input t = true) :
    busStep I h input (busWireOf I t) = some ((busPhase I h).front.out input t) := by
  rw [busStep_eq, busTr?_busWireOf I h input t hc, Option.bind_some,
    (busPhase I h).front.run_of_check hc]

/-- **On a transcript whose round polynomials pass their checks, the executable's verdict on its
wire is the oracle verifier's** on the transcript. -/
theorem busStep_busWireOf_of_solved (h : Bus.Conditions I) (input : I.Stmt)
    (t : (busSpec I).FullTranscript) (hs : BusSolved I input t) :
    busStep I h input (busWireOf I t) = (busPhase I h).front.run input t := by
  rw [busStep_eq, busTr?_busWireOf_of_solved I input t hs, Option.bind_some]

/-- At leanVM's instance the bus phase's algebra, with the program's share settled, is the
oracle verifier's run on the transcript the wire decodes to. -/
theorem leanVmBus_eq (prog : Program) (s : Sizes) (input : PublicInput) (w : BusWire) :
    leanVmBus prog s input w = (busTr? (leanVm prog s) input w).bind
      ((busPhase (leanVm prog s) (leanIsa_conditions _ prog s)).front.run input) := by
  rw [leanVmBus_eq_busStep, busStep_eq]

end Compile

end
end LeanerVM.Protocol
