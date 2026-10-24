/-
  LeanerVM.Protocol.Compile.Flock

  The executable verifier's Flock phase is the oracle verifier's: its algebra on the wire is the
  Flock phase's guarded verifier run on the transcript the wire decodes to, when the walk it
  evaluates the circuit's matrices by is the region's own.
-/

module

public import LeanerVM.Protocol.Compile.Tables
public import LeanerVM.Protocol.ToArkLib.Flock.Run

/-!
# The Flock phase on the wire

The executable verifier reads the Flock phase as its wire (`Verify.FlockWire`): the point's drawn
coordinates, the skip values, `z_skip`, the zerocheck's `m + κ` rounds (their constant
coefficients dropped), `â, b̂`, `α`, the lincheck's `m` rounds (their linear coefficients
dropped), the slices and the six ring-switching coefficients. The oracle verifier of the phase on
a region `r` (`flockPhaseSome`, the Flock slot of `leanVmPhases` at an instance with a region)
reads a transcript of `flockSpecOf r.kBatch`, where the zerocheck's rounds are two runs, the
within-block coordinates' and the batch coordinates'.

* `flockTr? I r s w`: the transcript the wire decodes to, every round polynomial rebuilt from its
  wire and the oracle verifier's running claim; `none` when the wire has another shape;
* `flockWireOf k t`: the wire read off a transcript.

**The Flock phase is the oracle verifier's** (`flockStep_eq`): when the walk `rows` the executable
evaluates the circuit's matrices by is the region's (`r.r1cs.rows`), its algebra is the oracle
verifier's guarded form run on the decoded transcript. At leanVM's instance the walk is
`blake2sRows`, the region's by `blake2sRows_eq_region` (`leanVmFlock_eq`). `flockStep_eq_some_iff`,
`flockTr?_flockWireOf` (an accepted transcript is the one its wire decodes to),
`flockWireOf_flockTr?` and `flockStep_flockWireOf` follow as for the other phases.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanIsa CompPoly CMlPolynomialEval ProtocolSpec
  SumcheckRound Verify

@[expose] public section

namespace Compile

/-! ## A replay in two parts -/

/-- A replay of rounds in two runs is the first run's, then the second's from its final claim. -/
theorem replayRounds_append {d : ℕ} {eq? : ℕ → Option E} :
    ∀ (j : ℕ) (claim : E) (rs₁ rs₂ : List Round),
      replayRounds d eq? j claim (rs₁ ++ rs₂) =
        (replayRounds d eq? j claim rs₁).bind fun p ↦
          (replayRounds d eq? (j + rs₁.length) p.1 rs₂).map fun q ↦ (q.1, p.2 ++ q.2)
  | j, claim, [], rs₂ => by
    simp only [List.nil_append, replayRounds, Option.bind_some, List.length_nil, Nat.add_zero]
    rcases replayRounds d eq? j claim rs₂ with _ | ⟨c, cs⟩ <;> rfl
  | j, claim, r :: rs₁, rs₂ => by
    simp only [List.cons_append, replayRounds, Option.bind_eq_bind, Option.pure_def]
    rcases RoundPoly.decode d claim (eq? j) r.wire with _ | q
    · rfl
    simp only [Option.bind_some]
    rw [replayRounds_append (j + 1) _ rs₁ rs₂]
    rcases replayRounds d eq? (j + 1) (RoundPoly.eval q r.chal) rs₁ with _ | ⟨c₁, cs₁⟩
    · rfl
    simp only [Option.bind_some, List.length_cons]
    rw [show j + (rs₁.length + 1) = j + 1 + rs₁.length by omega]
    rcases replayRounds d eq? (j + 1 + rs₁.length) c₁ rs₂ with _ | ⟨c₂, cs₂⟩
    · rfl
    · rfl

/-- A replay whose challenges fit no vector of the given length leaves nothing to read. -/
private theorem ofList?_eq_none_of_length {n : ℕ} {l : List E} (h : l.length ≠ n) :
    RoundPoly.ofList? n l = none :=
  Option.not_isSome_iff_eq_none.mp fun h' ↦ h (isSome_ofList?.mp h')

variable (I : M3Instance)


/-! ## Transcripts and wires -/

/-- The Flock phase's transcript for `2 ^ k` compressions from its parts. -/
def flockTrOf (k : ℕ) (v : Vector E (flockParams k).nRand) (msg : Vector E (2 ^ (flockParams k).s))
    (zskip : E) (zcL : (roundsSpec E 2 (flockParams k).m).FullTranscript)
    (zcH : (roundsSpec E 2 (flockParams k).κ).FullTranscript) (ab : Vector E 2) (α : E)
    (lin : (roundsSpec E 2 (flockParams k).m).FullTranscript)
    (sv : Vector E (2 ^ (flockParams k).s)) (fs : Vector E 6) : (flockSpecOf k).FullTranscript :=
  Flock.trOf (flockParams k) 5 v msg zskip zcL zcH ab α lin sv fs

/-- The Flock phase's wire for `2 ^ k` compressions, read off its transcript. -/
def flockWireOf (k : ℕ) (t : (Flock.flockSchedule E (flockParams k).s (flockParams k).m
    (flockParams k).κ (flockParams k).nRand 5).FullTranscript) : FlockWire :=
  let t₉ := t.fst
  let t₈ := t₉.fst
  let t₇ := t₈.fst
  let t₆ := t₇.fst
  let t₅ := t₆.fst
  let t₄ := t₅.fst
  let t₃ := t₄.fst
  let t₂ := t₃.fst
  let skip : Vector E (2 ^ (flockParams k).s) := t₂.snd 0
  let zskip : E := t₃.snd 0
  let ab : Vector E 2 := t₆.snd 0
  let α : E := t₇.snd 0
  let sv : Vector E (2 ^ (flockParams k).s) := t₉.snd 0
  ⟨chalsList (flockParams k).nRand t₂.fst, skip.toList, zskip,
    roundsWire 0 (flockParams k).m t₄.snd ++ roundsWire 0 (flockParams k).κ t₅.snd, ab.toList, α,
    roundsWire 1 (flockParams k).m t₈.snd, sv.toList, chalsList (5 + 1) t.snd⟩

/-- The wire of a Flock transcript in its parts. -/
theorem flockWireOf_flockTrOf (k : ℕ) (v : Vector E (flockParams k).nRand)
    (msg : Vector E (2 ^ (flockParams k).s)) (zskip : E)
    (zcL : (roundsSpec E 2 (flockParams k).m).FullTranscript)
    (zcH : (roundsSpec E 2 (flockParams k).κ).FullTranscript) (ab : Vector E 2) (α : E)
    (lin : (roundsSpec E 2 (flockParams k).m).FullTranscript)
    (sv : Vector E (2 ^ (flockParams k).s)) (fs : Vector E 6) :
    flockWireOf k (flockTrOf k v msg zskip zcL zcH ab α lin sv fs) =
      ⟨v.toList, msg.toList, zskip,
        roundsWire 0 (flockParams k).m zcL ++ roundsWire 0 (flockParams k).κ zcH, ab.toList, α,
        roundsWire 1 (flockParams k).m lin, sv.toList, fs.toList⟩ := by
  simp only [flockWireOf, flockTrOf, Flock.trOf, FullTranscript.append_fst,
    FullTranscript.append_snd, chalsList_chalsTr, ofFn_getElem_eq_toList, msgTr_zero,
    chalTr_zero]

/-- A Flock transcript is the transcript of its parts. -/
theorem exists_eq_flockTrOf (k : ℕ) (t : (flockSpecOf k).FullTranscript) :
    ∃ v msg zskip zcL zcH ab α lin sv fs, t = flockTrOf k v msg zskip zcL zcH ab α lin sv fs := by
  obtain ⟨v, msg, zskip, zcL, zcH, ab, α, lin, sv, fs, ht⟩ :=
    Flock.exists_eq_trOf (flockParams k) 5 t
  exact ⟨v, msg, zskip, zcL, zcH, ab, α, lin, sv, fs, ht⟩

/-! ## The decoding -/

/-- The transcript of the Flock phase on the region `r` its wire decodes to, from the public
input's output `s`: the point, the skip values, `z_skip`, the zerocheck's within-block and batch
rounds from `P(z_skip)` with the point's equality weights, `â, b̂`, `α`, the lincheck's rounds
from its batched claim, the slices and the ring-switching coefficients; `none` when the wire has
another shape. -/
def flockTr? (r : FlockRegion I.toShape) (s : I.Stmt × PubOut I) (w : FlockWire) :
    Option (flockSpecOf r.kBatch).FullTranscript :=
  let P := flockParams r.kBatch
  (RoundPoly.ofList? P.nRand w.point).bind fun v ↦
  (RoundPoly.ofList? (2 ^ P.s) w.skip).bind fun msg ↦
  (roundsTr? 2 (fun j ↦ (P.point v)[j]?) P.m 0 (Flock.skipClaim P.nodes msg w.zskip)
    (w.zc.take P.m)).bind fun zcL ↦
  (replayRounds 2 (fun j ↦ (P.point v)[j]?) 0 (Flock.skipClaim P.nodes msg w.zskip)
    (w.zc.take P.m)).bind fun pL ↦
  (roundsTr? 2 (fun j ↦ (P.point v)[j]?) P.κ P.m pL.1 (w.zc.drop P.m)).bind fun zcH ↦
  (replayRounds 2 (fun j ↦ (P.point v)[j]?) P.m pL.1 (w.zc.drop P.m)).bind fun pH ↦
  (RoundPoly.ofList? (P.m + P.κ) (pL.2 ++ pH.2)).bind fun χ ↦
  (RoundPoly.ofList? 2 w.ab).bind fun ab ↦
  (roundsTr? 2 (fun _ ↦ none) P.m 0
    (Flock.alphaNext (Flock.termNext (S := I.Stmt × PubOut I)
      ((s, P.point v, w.zskip), (χ, pH.1)) ab) w.alpha).2.2 w.lin).bind fun lin ↦
  (RoundPoly.ofList? (2 ^ P.s) w.slices).bind fun sv ↦
  (RoundPoly.ofList? 6 w.ring).map fun fs ↦
    flockTrOf r.kBatch v msg w.zskip zcL zcH ab w.alpha lin sv fs

/-! ## The run of the oracle verifier -/

/-- The zerocheck's family on the region `r`. -/
abbrev zcFam (r : FlockRegion I.toShape) :=
  Flock.zcFamily (flockParams r.kBatch) r.r1cs (FlockPhase.bits r) (FlockPhase.side (I := I))
    (W := Unit)

/-- The lincheck's family on the region `r`. -/
abbrev linFam (r : FlockRegion I.toShape) :=
  Flock.linFamily (flockParams r.kBatch) r.r1cs (FlockPhase.bits r) (FlockPhase.side (I := I))
    (W := Unit)

/-- The Flock phase's run on a transcript in its parts (`Flock.run_flockFront` on the region `r`):
the zerocheck's two runs of rounds from `P(z_skip)`, the lincheck's rounds from its batched claim,
the lincheck's check of the slices, and the switched weighted claim handed on. -/
theorem run_flockPhaseSome (r : FlockRegion I.toShape) (hr : I.flock = some r)
    (s : I.Stmt × PubOut I) (v : Vector E (flockParams r.kBatch).nRand)
    (msg : Vector E (2 ^ (flockParams r.kBatch).s)) (zskip : E)
    (zcL : (roundsSpec E 2 (flockParams r.kBatch).m).FullTranscript)
    (zcH : (roundsSpec E 2 (flockParams r.kBatch).κ).FullTranscript) (ab : Vector E 2) (α : E)
    (lin : (roundsSpec E 2 (flockParams r.kBatch).m).FullTranscript)
    (sv : Vector E (2 ^ (flockParams r.kBatch).s)) (fs : Vector E 6) :
    (flockPhaseSome I r hr).front.run s (flockTrOf r.kBatch v msg zskip zcL zcH ab α lin sv fs) =
      ((((roundsFront (zcFam I r).poly (zcFam I r).weight (flockParams r.kBatch).m
          (flockParams r.kBatch).m 0 (Nat.zero_add _)).run
          (Flock.skipNext (flockParams r.kBatch) ((s, v), msg) zskip) zcL).bind fun stL ↦
        (roundsFront (zcFam I r).poly (zcFam I r).weight
          ((flockParams r.kBatch).m + (flockParams r.kBatch).κ) (flockParams r.kBatch).κ
          (flockParams r.kBatch).m rfl).run stL zcH).bind fun stH ↦
        (roundsFront (linFam I r).poly (linFam I r).weight (flockParams r.kBatch).m
          (flockParams r.kBatch).m 0 (Nat.zero_add _)).run
          (Flock.alphaNext (Flock.termNext stH ab) α) lin).bind fun st ↦
        if Flock.linCheck (flockParams r.kBatch) r.r1cs st sv then
          some (FlockPhase.finish r hr (Flock.linNext (flockParams r.kBatch) st sv).1
            (Flock.ringWeight (flockParams r.kBatch) 5 (FlockPhase.lift r)
              (Flock.linNext (flockParams r.kBatch) st sv).2.1 fs)
            (Flock.ringTarget (flockParams r.kBatch) 5 (algebraMap K E) g
              (Flock.linNext (flockParams r.kBatch) st sv).2.2 fs))
        else none :=
  Flock.run_flockFront (flockParams r.kBatch) r.r1cs (FlockPhase.bits r) FlockPhase.side 5
    (algebraMap K E) g (FlockPhase.lift r) (FlockPhase.finish r hr) s v msg zskip zcL zcH ab α lin
    sv fs

/-- The point's equality weights are the oracle verifier's domains of the zerocheck's rounds. -/
private theorem zc_weights_eq (r : FlockRegion I.toShape)
    (x : Flock.ZcX (I.Stmt × PubOut I) E ((flockParams r.kBatch).m + (flockParams r.kBatch).κ))
    (k : ℕ) (hk : k < (flockParams r.kBatch).m + (flockParams r.kBatch).κ) :
    (zcFam I r).weight x k = eqDomain (x.2.1[k]?) := by
  simp [zcFam, Flock.zcFamily, SumcheckRound.normalizedWeights, hk, eqDomain]

/-- The plain domain is the oracle verifier's domain of every lincheck round. -/
private theorem lin_weights_eq (r : FlockRegion I.toShape)
    (x : Flock.LinX (I.Stmt × PubOut I) E ((flockParams r.kBatch).m + (flockParams r.kBatch).κ))
    (k : ℕ) : (linFam I r).weight x k = eqDomain none :=
  rfl

/-- The zerocheck's rounds drop their constant coefficients. -/
private theorem zc_dropped (r : FlockRegion I.toShape)
    (pt : Vector E ((flockParams r.kBatch).m + (flockParams r.kBatch).κ)) (k : ℕ)
    (hk : k < (flockParams r.kBatch).m + (flockParams r.kBatch).κ) :
    RoundPoly.dropped (pt[k]?) = 0 := by
  simp [RoundPoly.dropped, hk]

/-- **The executable verifier's Flock phase is the oracle verifier's**: when the walk `rows` it
evaluates the circuit's matrices by is the region's, its algebra on the wire is the Flock phase's
guarded verifier run on the transcript the wire decodes to. -/
theorem flockStep_eq (r : FlockRegion I.toShape) (hr : I.flock = some r)
    (rows : CMlPolynomialEval E (Flock.kSkip + Flock.kIn) →
      CMlPolynomialEval E (Flock.kSkip + Flock.kIn) × CMlPolynomialEval E (Flock.kSkip + Flock.kIn))
    (hrows : ∀ x, rows x = r.r1cs.rows x) (s : I.Stmt × PubOut I) (w : FlockWire) :
    flockStep I r hr rows s w = (flockTr? I r s w).bind ((flockPhaseSome I r hr).front.run s) := by
  obtain rfl : rows = r.r1cs.rows := funext hrows
  simp only [flockStep, flockTr?, Option.bind_eq_bind]
  rcases RoundPoly.ofList? (flockParams r.kBatch).nRand w.point with _ | v
  · rfl
  rcases RoundPoly.ofList? (2 ^ (flockParams r.kBatch).s) w.skip with _ | msg
  · rfl
  simp only [Option.bind_some]
  have hsplit := replayRounds_append (d := 2) (eq? := fun j ↦ ((flockParams r.kBatch).point v)[j]?)
    0 (Flock.skipClaim (flockParams r.kBatch).nodes msg w.zskip)
    (w.zc.take (flockParams r.kBatch).m) (w.zc.drop (flockParams r.kBatch).m)
  rw [List.take_append_drop] at hsplit
  rw [hsplit]
  rcases hL : roundsTr? 2 (fun j ↦ ((flockParams r.kBatch).point v)[j]?) (flockParams r.kBatch).m 0
      (Flock.skipClaim (flockParams r.kBatch).nodes msg w.zskip)
      (w.zc.take (flockParams r.kBatch).m) with _ | zcL
  · simp only [Option.bind_none]
    by_cases hlen : (w.zc.take (flockParams r.kBatch).m).length = (flockParams r.kBatch).m
    · rw [replayRounds_eq_none _ _ 0 _ _ hlen hL]
      rfl
    · rcases hrL : replayRounds 2 (fun j ↦ ((flockParams r.kBatch).point v)[j]?) 0
          (Flock.skipClaim (flockParams r.kBatch).nodes msg w.zskip)
          (w.zc.take (flockParams r.kBatch).m) with _ | ⟨cL, csL⟩
      · rfl
      simp only [Option.bind_some]
      rcases hrH : replayRounds 2 (fun j ↦ ((flockParams r.kBatch).point v)[j]?)
          (0 + (w.zc.take (flockParams r.kBatch).m).length) cL
          (w.zc.drop (flockParams r.kBatch).m) with _ | ⟨cH, csH⟩
      · rfl
      simp only [Option.map_some, Option.bind_some]
      rw [ofList?_eq_none_of_length]
      · rfl
      · rw [List.length_append, length_of_replayRounds hrL, length_of_replayRounds hrH]
        simp only [List.length_take, List.length_drop] at hlen ⊢
        omega
  have hlenL := length_of_roundsTr? _ hL
  obtain ⟨cL, csL, hrL, vL, hvL, hrunL⟩ := run_roundsTr (zcFam I r).poly (zcFam I r).weight
    (fun j ↦ ((flockParams r.kBatch).point v)[j]?) (flockParams r.kBatch).m
    (flockParams r.kBatch).m 0 (Nat.zero_add _)
    (((s, (flockParams r.kBatch).point v, w.zskip),
      (#v[], Flock.skipClaim (flockParams r.kBatch).nodes msg w.zskip)) :
      Stmt (Flock.ZcX (I.Stmt × PubOut I) E ((flockParams r.kBatch).m + (flockParams r.kBatch).κ))
        E 0)
    (w.zc.take (flockParams r.kBatch).m) zcL
    (fun k _ hk ↦ zc_weights_eq I r _ k (by omega)) hL
  rw [hrL]
  simp only [Option.bind_some]
  rw [show 0 + (w.zc.take (flockParams r.kBatch).m).length = (flockParams r.kBatch).m by
    rw [hlenL]; rfl]
  rcases hH : roundsTr? 2 (fun j ↦ ((flockParams r.kBatch).point v)[j]?) (flockParams r.kBatch).κ
      (flockParams r.kBatch).m cL (w.zc.drop (flockParams r.kBatch).m) with _ | zcH
  · simp only [Option.bind_none]
    by_cases hlen : (w.zc.drop (flockParams r.kBatch).m).length = (flockParams r.kBatch).κ
    · rw [replayRounds_eq_none _ _ _ _ _ hlen hH]
      rfl
    · rcases hrH : replayRounds 2 (fun j ↦ ((flockParams r.kBatch).point v)[j]?)
          (flockParams r.kBatch).m cL (w.zc.drop (flockParams r.kBatch).m) with _ | ⟨cH, csH⟩
      · rfl
      simp only [Option.map_some, Option.bind_some]
      rw [ofList?_eq_none_of_length]
      · rfl
      · rw [List.length_append, length_of_replayRounds hrL, length_of_replayRounds hrH, hlenL]
        exact fun h ↦ hlen (by omega)
  obtain ⟨cH, csH, hrH, vH, hvH, hrunH⟩ := run_roundsTr (zcFam I r).poly (zcFam I r).weight
    (fun j ↦ ((flockParams r.kBatch).point v)[j]?)
    ((flockParams r.kBatch).m + (flockParams r.kBatch).κ) (flockParams r.kBatch).κ
    (flockParams r.kBatch).m rfl
    (((s, (flockParams r.kBatch).point v, w.zskip), (vL, cL)) :
      Stmt (Flock.ZcX (I.Stmt × PubOut I) E ((flockParams r.kBatch).m + (flockParams r.kBatch).κ))
        E (flockParams r.kBatch).m)
    (w.zc.drop (flockParams r.kBatch).m) zcH
    (fun k _ hk ↦ zc_weights_eq I r _ k hk) hH
  rw [hrH]
  simp only [Option.map_some, Option.bind_some]
  have hχ : RoundPoly.ofList? ((flockParams r.kBatch).m + (flockParams r.kBatch).κ)
      (csL ++ csH) = some vH := by
    rw [← ofList?_toList vH, hvH, hvL]
    rfl
  rw [hχ, Option.bind_some]
  rcases RoundPoly.ofList? 2 w.ab with _ | ab
  · rfl
  simp only [Option.bind_some]
  rcases hLin : roundsTr? 2 (fun _ ↦ none) (flockParams r.kBatch).m 0
      (Flock.alphaNext (Flock.termNext (S := I.Stmt × PubOut I)
        ((s, (flockParams r.kBatch).point v, w.zskip), (vH, cH)) ab) w.alpha).2.2 w.lin
      with _ | lin
  · simp only [Option.bind_none]
    by_cases hlen : w.lin.length = (flockParams r.kBatch).m
    · rw [replayRounds_eq_none _ _ _ _ _ hlen hLin]
      rfl
    · rcases hrLin : replayRounds 2 (fun _ ↦ none) 0
          (Flock.alphaNext (Flock.termNext (S := I.Stmt × PubOut I)
            ((s, (flockParams r.kBatch).point v, w.zskip), (vH, cH)) ab) w.alpha).2.2 w.lin
          with _ | ⟨cLin, csLin⟩
      · rfl
      simp only [Option.bind_some]
      rw [ofList?_eq_none_of_length]
      · rfl
      · rw [length_of_replayRounds hrLin]
        exact hlen
  obtain ⟨cLin, csLin, hrLin, vLin, hvLin, hrunLin⟩ := run_roundsTr (linFam I r).poly
    (linFam I r).weight (fun _ ↦ none) (flockParams r.kBatch).m (flockParams r.kBatch).m 0
    (Nat.zero_add _)
    (Flock.alphaNext (Flock.termNext (S := I.Stmt × PubOut I)
      ((s, (flockParams r.kBatch).point v, w.zskip), (vH, cH)) ab) w.alpha) w.lin lin
    (fun k _ _ ↦ lin_weights_eq I r _ k) hLin
  have hcLin : RoundPoly.ofList? (flockParams r.kBatch).m csLin = some vLin := by
    rw [← ofList?_toList vLin, hvLin]
    rfl
  rw [hrLin]
  simp only [Option.bind_some, hcLin]
  rcases RoundPoly.ofList? (2 ^ (flockParams r.kBatch).s) w.slices with _ | sv
  · rfl
  simp only [Option.bind_some]
  rcases RoundPoly.ofList? 6 w.ring with _ | fs
  · split_ifs <;> rfl
  simp only [Option.map_some, Option.bind_some]
  rw [run_flockPhaseSome]
  erw [hrunL]
  simp only [Option.bind_some]
  erw [hrunH]
  simp only [Option.bind_some]
  erw [hrunLin]
  simp only [Option.bind_some]
  split_ifs with h₁ h₂ h₂ <;> first
    | rfl
    | exact absurd (of_decide_eq_true h₂) h₁
    | exact absurd (decide_eq_true (not_not.mp h₁)) h₂

/-- The executable accepts the Flock phase's wire exactly when the transcript it decodes to
exists and the oracle verifier accepts it, with the oracle verifier's output. -/
theorem flockStep_eq_some_iff (r : FlockRegion I.toShape) (hr : I.flock = some r)
    (rows : CMlPolynomialEval E (Flock.kSkip + Flock.kIn) →
      CMlPolynomialEval E (Flock.kSkip + Flock.kIn) × CMlPolynomialEval E (Flock.kSkip + Flock.kIn))
    (hrows : ∀ x, rows x = r.r1cs.rows x) (s : I.Stmt × PubOut I) (w : FlockWire)
    (o : I.Stmt × FlockOut I) :
    flockStep I r hr rows s w = some o ↔ ∃ t, flockTr? I r s w = some t ∧
      (flockPhaseSome I r hr).front.check s t = true ∧
        (flockPhaseSome I r hr).front.out s t = o := by
  rw [flockStep_eq I r hr rows hrows, Option.bind_eq_some_iff]
  exact exists_congr fun t ↦ and_congr_right fun _ ↦ Component.Front.run_eq_some_iff _

/-- A transcript of the Flock phase the oracle verifier accepts is the one its wire decodes
to. -/
theorem flockTr?_flockWireOf (r : FlockRegion I.toShape) (hr : I.flock = some r)
    (s : I.Stmt × PubOut I) (t : (flockSpecOf r.kBatch).FullTranscript)
    (hc : (flockPhaseSome I r hr).front.check s t = true) :
    flockTr? I r s (flockWireOf r.kBatch t) = some t := by
  obtain ⟨v, msg, zskip, zcL, zcH, ab, α, lin, sv, fs, rfl⟩ := exists_eq_flockTrOf r.kBatch t
  have hrun := (flockPhaseSome I r hr).front.run_of_check hc
  rw [run_flockPhaseSome] at hrun
  obtain ⟨st, hst, -⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨stH, hstH, hLin⟩ := Option.bind_eq_some_iff.mp hst
  obtain ⟨stL, hL, hH⟩ := Option.bind_eq_some_iff.mp hstH
  have hRL := roundsTr?_roundsWire (zcFam I r).poly (zcFam I r).weight
    (fun j ↦ ((flockParams r.kBatch).point v)[j]?) (flockParams r.kBatch).m (by norm_num) 0
    (flockParams r.kBatch).m 0 (Nat.zero_add _)
    (((s, (flockParams r.kBatch).point v, zskip),
      (#v[], Flock.skipClaim (flockParams r.kBatch).nodes msg zskip)) :
      Stmt (Flock.ZcX (I.Stmt × PubOut I) E ((flockParams r.kBatch).m + (flockParams r.kBatch).κ))
        E 0) zcL
    (fun k _ hk ↦ zc_weights_eq I r _ k (by omega))
    (fun k _ hk ↦ zc_dropped I r _ k (by omega))
    ((Component.Front.run_eq_some_iff _).mp hL).1
  obtain ⟨cL, csL, hrL, vL, hvL, hrunL⟩ := run_roundsTr (zcFam I r).poly (zcFam I r).weight
    (fun j ↦ ((flockParams r.kBatch).point v)[j]?) (flockParams r.kBatch).m
    (flockParams r.kBatch).m 0 (Nat.zero_add _)
    (((s, (flockParams r.kBatch).point v, zskip),
      (#v[], Flock.skipClaim (flockParams r.kBatch).nodes msg zskip)) :
      Stmt (Flock.ZcX (I.Stmt × PubOut I) E ((flockParams r.kBatch).m + (flockParams r.kBatch).κ))
        E 0) _ zcL
    (fun k _ hk ↦ zc_weights_eq I r _ k (by omega)) hRL
  have hL' := hL
  erw [hrunL, Option.some.injEq] at hL'
  subst hL'
  have hRH := roundsTr?_roundsWire (zcFam I r).poly (zcFam I r).weight
    (fun j ↦ ((flockParams r.kBatch).point v)[j]?)
    ((flockParams r.kBatch).m + (flockParams r.kBatch).κ) (by norm_num) 0
    (flockParams r.kBatch).κ (flockParams r.kBatch).m rfl
    (((s, (flockParams r.kBatch).point v, zskip), (vL, cL)) :
      Stmt (Flock.ZcX (I.Stmt × PubOut I) E ((flockParams r.kBatch).m + (flockParams r.kBatch).κ))
        E (flockParams r.kBatch).m) zcH
    (fun k _ hk ↦ zc_weights_eq I r _ k hk) (fun k _ hk ↦ zc_dropped I r _ k hk)
    ((Component.Front.run_eq_some_iff _).mp hH).1
  obtain ⟨cH, csH, hrH, vH, hvH, hrunH⟩ := run_roundsTr (zcFam I r).poly (zcFam I r).weight
    (fun j ↦ ((flockParams r.kBatch).point v)[j]?)
    ((flockParams r.kBatch).m + (flockParams r.kBatch).κ) (flockParams r.kBatch).κ
    (flockParams r.kBatch).m rfl
    (((s, (flockParams r.kBatch).point v, zskip), (vL, cL)) :
      Stmt (Flock.ZcX (I.Stmt × PubOut I) E ((flockParams r.kBatch).m + (flockParams r.kBatch).κ))
        E (flockParams r.kBatch).m) _ zcH
    (fun k _ hk ↦ zc_weights_eq I r _ k hk) hRH
  have hH' := hH
  erw [hrunH, Option.some.injEq] at hH'
  subst hH'
  have hRLin := roundsTr?_roundsWire (linFam I r).poly (linFam I r).weight (fun _ ↦ none)
    (flockParams r.kBatch).m (by norm_num) 1 (flockParams r.kBatch).m 0 (Nat.zero_add _)
    (Flock.alphaNext (Flock.termNext (S := I.Stmt × PubOut I)
      ((s, (flockParams r.kBatch).point v, zskip), (vH, cH)) ab) α) lin
    (fun k _ _ ↦ lin_weights_eq I r _ k) (fun _ _ _ ↦ rfl)
    ((Component.Front.run_eq_some_iff _).mp hLin).1
  have hχ : RoundPoly.ofList? ((flockParams r.kBatch).m + (flockParams r.kBatch).κ)
      (csL ++ csH) = some vH := by
    rw [← ofList?_toList vH, hvH, hvL]
    rfl
  have hlenL := length_roundsWire 0 (flockParams r.kBatch).m zcL
  rw [flockWireOf_flockTrOf]
  simp only [flockTr?]
  rw [ofList?_toList v, Option.bind_some, ofList?_toList msg, Option.bind_some,
    List.take_left' hlenL, List.drop_left' hlenL, hRL, Option.bind_some, hrL, Option.bind_some,
    hRH, Option.bind_some, hrH, Option.bind_some, hχ, Option.bind_some, ofList?_toList ab,
    Option.bind_some, hRLin, Option.bind_some, ofList?_toList sv, Option.bind_some,
    ofList?_toList fs, Option.map_some]

/-- The transcript the Flock phase's wire decodes to carries the wire. -/
theorem flockWireOf_flockTr? {r : FlockRegion I.toShape} {s : I.Stmt × PubOut I}
    {w : FlockWire} {t : (flockSpecOf r.kBatch).FullTranscript} (h : flockTr? I r s w = some t) :
    flockWireOf r.kBatch t = w := by
  simp only [flockTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, msg, hmsg, zcL, hzcL, pL, -, zcH, hzcH, pH, -, χ, -, ab, hab, lin, hlin, sv, hsv,
    fs, hfs, rfl⟩ := h
  rcases w with ⟨point, skip, zskip, zc, wab, alpha, wlin, slices, ring⟩
  simp only at hv hmsg hzcL hzcH hab hlin hsv hfs
  rw [flockWireOf_flockTrOf]
  have hL := roundsWire_roundsTr? _ 0 _ 0 _ _ zcL
    (fun k _ hk ↦ zc_dropped I r _ k (by omega)) hzcL
  have hH := roundsWire_roundsTr? _ 0 _ _ _ _ zcH
    (fun k _ hk ↦ zc_dropped I r _ k hk) hzcH
  have hLin := roundsWire_roundsTr? (fun _ ↦ none) 1 _ 0 _ _ lin (fun _ _ _ ↦ rfl) hlin
  rw [hL, hH, hLin, List.take_append_drop, toList_of_ofList? hv, toList_of_ofList? hmsg,
    toList_of_ofList? hab, toList_of_ofList? hsv, toList_of_ofList? hfs]

/-- **On a transcript the oracle verifier accepts, the executable accepts its wire** with the
oracle verifier's output, when its walk is the region's. -/
theorem flockStep_flockWireOf (r : FlockRegion I.toShape) (hr : I.flock = some r)
    (rows : CMlPolynomialEval E (Flock.kSkip + Flock.kIn) →
      CMlPolynomialEval E (Flock.kSkip + Flock.kIn) × CMlPolynomialEval E (Flock.kSkip + Flock.kIn))
    (hrows : ∀ x, rows x = r.r1cs.rows x) (s : I.Stmt × PubOut I)
    (t : (flockSpecOf r.kBatch).FullTranscript)
    (hc : (flockPhaseSome I r hr).front.check s t = true) :
    flockStep I r hr rows s (flockWireOf r.kBatch t) =
      some ((flockPhaseSome I r hr).front.out s t) := by
  rw [flockStep_eq I r hr rows hrows, flockTr?_flockWireOf I r hr s t hc, Option.bind_some,
    (flockPhaseSome I r hr).front.run_of_check hc]

/-- At leanVM's instance the verifier's BLAKE2s walk is the region's: the region carries the
circuit's R1CS on words (`ProductCircuit.toBlockR1CSE`), equal to its block R1CS
(`toBlockR1CSE_eq`), whose walk `blake2sRows` is (`blake2sRows_eq`). -/
theorem blake2sRows_eq_region (prog : Program) (sz : Sizes)
    (x : CompPoly.CMlPolynomialEval E (Flock.kSkip + Flock.kIn)) :
    blake2sRows x = (flockRegion prog sz Blake2sFlock.blake2sFlockSpec).r1cs.rows x := by
  rw [blake2sRows_eq]
  exact congrArg (fun R ↦ BlockR1CS.rows R x)
    (ProductCircuit.toBlockR1CSE_eq Blake2sCircuit.blake2sCircuit).symm

/-- At leanVM's instance the Flock phase's algebra, with the BLAKE2s circuit's walk
`blake2sRows`, is the oracle verifier's run on the transcript the wire decodes to. -/
theorem leanVmFlock_eq (prog : Program) (sz : Sizes) (s : PublicInput × PubOut (leanVm prog sz))
    (w : FlockWire) :
    flockStep (leanVm prog sz) (flockRegion prog sz Blake2sFlock.blake2sFlockSpec) rfl blake2sRows
        s w =
      (flockTr? (leanVm prog sz) (flockRegion prog sz Blake2sFlock.blake2sFlockSpec) s w).bind
        ((flockPhaseSome (leanVm prog sz) (flockRegion prog sz Blake2sFlock.blake2sFlockSpec)
          rfl).front.run s) :=
  flockStep_eq (leanVm prog sz) (flockRegion prog sz Blake2sFlock.blake2sFlockSpec) rfl
    blake2sRows (blake2sRows_eq_region prog sz) s w

end Compile

end
end LeanerVM.Protocol
