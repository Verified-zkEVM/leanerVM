/-
  LeanerVM.Protocol.Compile.Rounds

  Sumcheck rounds on the wire and in the oracle protocol: the executable verifier's evaluation and
  round check are the oracle verifier's, and the rounds it replays from their wires are the oracle
  verifier's run on the transcript the wires decode to.
-/

module

public import LeanerVM.Protocol.Verify.Setup
public import LeanerVM.Protocol.ToArkLib.FrontRun

/-!
# Sumcheck rounds on the wire

The executable verifier reads a round polynomial as its wire, the coefficients but the one the
chain does not absorb, and rebuilds the dropped one from the running claim (`RoundPoly.decode`,
`LeanerVM.Protocol.Proof`). The oracle verifier of a round (`SumcheckRound.round`) reads all the
coefficients and checks their weighted sum over the round's domain against the running claim.
On the round's domain (`eqDomain`: `0, 1` with unit weights, or with `1 - r, r` when the equality
weight `r` is factored out) the executable's check is the oracle verifier's (`check_iff`), and so
is its evaluation (`eval_eq_evaluate`).

`roundsTr? d eq? i j claim rs` is the transcript of `i` rounds that the wires `rs` decode to, from
round `j` at the claim `claim`: each polynomial rebuilt from its wire and the running claim, each
challenge evaluating it into the next claim. `roundsWire drop i t` reads the wires back off a
transcript, coefficient `drop` left out. Then

* `run_roundsTr`: on the transcript the wires decode to, the oracle verifier of the rounds
  accepts, and its verdict is what the executable's `replayRounds` computes: the final claim and
  the challenges after the statement's;
* `replayRounds_eq_none`: wires of the right number that do not decode do not replay;
* `roundsTr?_roundsWire`: a transcript the oracle verifier accepts is the one its wires decode to;
* `roundsWire_roundsTr?`: the transcript the wires decode to carries them.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters ProtocolSpec SumcheckRound Verify

@[expose] public section

namespace Compile

/-! ## One round -/

/-- The weighted domain of a round whose equality weight is `eq?`: `0, 1` with unit weights in a
plain round, with the weights `1 - r, r` when `r` is factored out. -/
def eqDomain : Option E → WeightedDomain E
  | none => [(0, 1), (1, 1)]
  | some r => [(0, 1 - r), (1, r)]

/-- Horner's evaluation is the sum of the monomials. -/
private theorem evalList_eq_sum (x : E) :
    ∀ l : List E, RoundPoly.evalList l x = ∑ i ∈ Finset.range l.length, l.getD i 0 * x ^ i
  | [] => by simp [RoundPoly.evalList]
  | c :: l => by
    rw [RoundPoly.evalList, evalList_eq_sum x l, List.length_cons, Finset.sum_range_succ',
      Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    exact congrArg (· + c) (Finset.sum_congr rfl fun i _ ↦ by ring)

/-- The executable's evaluation of a round polynomial is the oracle verifier's. -/
theorem eval_eq_evaluate {d : ℕ} (c : Vector E (d + 1)) (x : E) :
    RoundPoly.eval c x = evaluate d c x := by
  rw [RoundPoly.eval, evalList_eq_sum, Vector.length_toList, evaluate,
    ← Fin.sum_univ_eq_sum_range (fun i ↦ c.toList.getD i 0 * x ^ i)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [List.getD_eq_getElem?_getD, Vector.getElem?_toList, Vector.getElem?_eq_getElem i.isLt,
    Option.getD_some]
  rfl

/-- **The executable's round check is the oracle verifier's** on the round's domain. -/
theorem check_iff {d : ℕ} (claim : E) (eq? : Option E) (c : Vector E (d + 1)) :
    RoundPoly.Check claim eq? c ↔ weightedSum d (eqDomain eq?) c = claim := by
  cases eq? with
  | none =>
    simp [RoundPoly.Check, weightedSum, eqDomain, eval_eq_evaluate]
  | some r =>
    simp [RoundPoly.Check, weightedSum, eqDomain, eval_eq_evaluate, CharTwo.sub_eq_add]

/-- A wire decodes to a polynomial exactly when the polynomial carries the wire and passes its
round's check, at a positive degree. -/
theorem decode_eq_some_iff {d : ℕ} {claim : E} {eq? : Option E} {w : List E}
    {c : Vector E (d + 1)} :
    RoundPoly.decode d claim eq? w = some c ↔
      0 < d ∧ RoundPoly.encode eq? c = w ∧ RoundPoly.Check claim eq? c := by
  refine ⟨fun h ↦ ⟨?_, RoundPoly.encode_decode h, RoundPoly.check_of_decode h⟩, ?_⟩
  · unfold RoundPoly.decode at h
    split at h
    · rename_i hd
      exact hd.1
    · cases h
  · rintro ⟨hd, rfl, hc⟩
    exact RoundPoly.decode_encode hd hc

/-! ## Runs of rounds -/

/-- A round polynomial's wire, the coefficient at `drop` left out. -/
def polyWire {d : ℕ} (drop : ℕ) (p : Vector E (d + 1)) : List E := p.toList.eraseIdx drop

/-- The wires of a run of rounds, coefficient `drop` left out of every polynomial. -/
def roundsWire {d : ℕ} (drop : ℕ) : (i : ℕ) → (roundsSpec E d i).FullTranscript → List Round
  | 0, _ => []
  | i + 1, t =>
    ⟨polyWire drop
        ((FullTranscript.fst (pSpec₁ := roundSpec E d) (pSpec₂ := roundsSpec E d i) t).fst 0),
      (FullTranscript.fst (pSpec₁ := roundSpec E d) (pSpec₂ := roundsSpec E d i) t).snd 0⟩ ::
      roundsWire drop i
        (FullTranscript.snd (pSpec₁ := roundSpec E d) (pSpec₂ := roundsSpec E d i) t)

/-- The transcript of `i` rounds the wires `rs` decode to, from round `j` at the claim `claim`:
each polynomial rebuilt from its wire and the running claim with the equality weight `eq? j` of
its round, each challenge evaluating it into the next claim; `none` for another number of rounds
or a wire that does not decode. -/
def roundsTr? (d : ℕ) (eq? : ℕ → Option E) :
    (i : ℕ) → ℕ → E → List Round → Option ((roundsSpec E d i).FullTranscript)
  | 0, _, _, [] => some nilTr
  | 0, _, _, _ :: _ => none
  | _ + 1, _, _, [] => none
  | i + 1, j, claim, r :: rs =>
    (RoundPoly.decode d claim (eq? j) r.wire).bind fun q ↦
      (roundsTr? d eq? i (j + 1) (RoundPoly.eval q r.chal) rs).map (roundsCons q r.chal)

variable {X : Type} {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] {W : Type} {d : ℕ}
  (P : Polys E X O W d) (wt : Weights E X) (eq? : ℕ → Option E)

/-- **The rounds the executable replays are the oracle verifier's run** on the transcript their
wires decode to, when the oracle verifier's domain at each of the rounds is the round's
(`eqDomain`): the run accepts, and its verdict is the statement with the challenges after its own
and the final claim the replay computes. -/
theorem run_roundsTr (m : ℕ) :
    ∀ (i j : ℕ) (h : j + i = m) (s : Stmt X E j) (rs : List Round)
      (t : (roundsSpec E d i).FullTranscript),
      (∀ k, j ≤ k → k < j + i → wt s.1 k = eqDomain (eq? k)) →
      roundsTr? d eq? i j s.2.2 rs = some t →
      ∃ final cs, replayRounds d eq? j s.2.2 rs = some (final, cs) ∧
        ∃ v : Vector E m, v.toList = s.2.1.toList ++ cs ∧
          (roundsFront P wt m i j h).run s t = some (s.1, (v, final))
  | 0, j, h, s, rs, t, _, ht => by
    rcases rs with _ | ⟨r, rs⟩
    · refine ⟨s.2.2, [], rfl, Vector.cast (by omega) s.2.1, by simp [Vector.toList_cast], ?_⟩
      exact run_roundsFront_zero P wt m j h s t
    · nomatch ht
  | i + 1, j, h, s, rs, t, hwt, ht => by
    rcases rs with _ | ⟨r, rs⟩
    · nomatch ht
    simp only [roundsTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ht
    obtain ⟨q, hq, t', ht', rfl⟩ := ht
    have hcheck : check j wt s q = true := by
      rw [check, decide_eq_true_iff, hwt j le_rfl (by omega), ← check_iff]
      exact RoundPoly.check_of_decode hq
    obtain ⟨final, cs, hrep, v, hv, hrun⟩ :=
      run_roundsTr m i (j + 1) (by omega) (next j s (evaluate d q r.chal) r.chal) rs t'
        (fun k hk hk' ↦ hwt k (by omega) (by omega))
        (by rw [show (next j s (evaluate d q r.chal) r.chal).2.2 = RoundPoly.eval q r.chal from
          (eval_eq_evaluate q r.chal).symm]; exact ht')
    refine ⟨final, r.chal :: cs, ?_, v, ?_, ?_⟩
    · simp only [replayRounds, Option.bind_eq_bind, hq, Option.bind_some]
      rw [show RoundPoly.eval q r.chal = (next j s (evaluate d q r.chal) r.chal).2.2 from
        eval_eq_evaluate q r.chal, hrep]
      rfl
    · rw [hv]
      simp [next, Vector.toList_push]
    · rw [run_roundsFront_succ]
      simp only [hcheck, ↓reduceIte]
      exact hrun

/-- Wires of the right number that do not decode do not replay: one of them has another length,
or the degree is `0`. -/
theorem replayRounds_eq_none :
    ∀ (i j : ℕ) (claim : E) (rs : List Round), rs.length = i →
      roundsTr? d eq? i j claim rs = none → replayRounds d eq? j claim rs = none
  | 0, j, claim, [], _, ht => nomatch ht
  | i + 1, j, claim, r :: rs, hl, ht => by
    simp only [roundsTr?, Option.bind_eq_none_iff, Option.map_eq_none_iff] at ht
    simp only [replayRounds, Option.bind_eq_bind]
    rcases hq : RoundPoly.decode d claim (eq? j) r.wire with _ | q
    · rfl
    · rw [Option.bind_some, replayRounds_eq_none i (j + 1) _ rs (by simpa using hl) (ht q hq)]
      rfl

/-- Wires that decode are one per round. -/
theorem length_of_roundsTr? :
    ∀ {i j : ℕ} {claim : E} {rs : List Round} {t : (roundsSpec E d i).FullTranscript},
      roundsTr? d eq? i j claim rs = some t → rs.length = i
  | 0, _, _, [], _, _ => rfl
  | 0, _, _, _ :: _, _, h => nomatch h
  | _ + 1, _, _, [], _, h => nomatch h
  | i + 1, j, claim, r :: rs, t, h => by
    simp only [roundsTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨q, -, t', ht', -⟩ := h
    simp [length_of_roundsTr? ht']

/-- The wires of `i` rounds are `i`. -/
theorem length_roundsWire (drop : ℕ) : ∀ (i : ℕ) (t : (roundsSpec E d i).FullTranscript),
    (roundsWire drop i t).length = i
  | 0, _ => rfl
  | i + 1, t => by simp [roundsWire, length_roundsWire drop i]

/-- A transcript whose rounds the oracle verifier accepts is the transcript its wires decode to,
at a positive degree, when the oracle verifier's domain at each of the rounds is the round's and
the coefficient left out is the one the round drops. -/
theorem roundsTr?_roundsWire (m : ℕ) (hd : 0 < d) (drop : ℕ) :
    ∀ (i j : ℕ) (h : j + i = m) (s : Stmt X E j) (t : (roundsSpec E d i).FullTranscript),
      (∀ k, j ≤ k → k < j + i → wt s.1 k = eqDomain (eq? k)) →
      (∀ k, j ≤ k → k < j + i → RoundPoly.dropped (eq? k) = drop) →
      (roundsFront P wt m i j h).check s t = true →
      roundsTr? d eq? i j s.2.2 (roundsWire drop i t) = some t
  | 0, j, h, s, t, _, _, _ => by
    rw [roundsWire, roundsTr?, eq_nilTr t]
  | i + 1, j, h, s, t, hwt, hdrop, hc => by
    obtain ⟨q, c, t', rfl⟩ : ∃ q c t', t = roundsCons q c t' := ⟨_, _, _, eq_roundsCons t⟩
    have hrun := (roundsFront P wt m (i + 1) j h).run_of_check hc
    rw [run_roundsFront_succ] at hrun
    split at hrun
    · rename_i hcheck
      rw [check, decide_eq_true_iff, hwt j le_rfl (by omega), ← check_iff] at hcheck
      have hdec : RoundPoly.decode d s.2.2 (eq? j) (polyWire drop q) = some q := by
        rw [polyWire, ← hdrop j le_rfl (by omega)]
        exact RoundPoly.decode_encode hd hcheck
      have ih := roundsTr?_roundsWire m hd drop i (j + 1) (by omega)
        (next j s (evaluate d q c) c) t'
        (fun k hk hk' ↦ hwt k (by omega) (by omega)) (fun k hk hk' ↦ hdrop k (by omega) (by omega))
        ((Component.Front.run_eq_some_iff _).mp hrun).1
      have hw : roundsWire drop (i + 1) (roundsCons q c t') =
          ⟨polyWire drop q, c⟩ :: roundsWire drop i t' := by
        simp only [roundsWire, roundsCons, roundTr, FullTranscript.append_fst,
          FullTranscript.append_snd, msgTr_zero, chalTr_zero]
      rw [hw]
      simp only [roundsTr?, hdec, Option.bind_some]
      rw [show RoundPoly.eval q c = (next j s (evaluate d q c) c).2.2 from eval_eq_evaluate _ _,
        ih]
      rfl
    · exact absurd hrun (by simp)

/-- The transcript the wires decode to carries them, when the coefficient left out is the one
each round drops. -/
theorem roundsWire_roundsTr? (drop : ℕ) :
    ∀ (i j : ℕ) (claim : E) (rs : List Round) (t : (roundsSpec E d i).FullTranscript),
      (∀ k, j ≤ k → k < j + i → RoundPoly.dropped (eq? k) = drop) →
      roundsTr? d eq? i j claim rs = some t → roundsWire drop i t = rs
  | 0, j, claim, [], t, _, _ => rfl
  | 0, j, claim, _ :: _, t, _, ht => nomatch ht
  | i + 1, j, claim, [], t, _, ht => nomatch ht
  | i + 1, j, claim, r :: rs, t, hdrop, ht => by
    simp only [roundsTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ht
    obtain ⟨q, hq, t', ht', rfl⟩ := ht
    have ih := roundsWire_roundsTr? drop i (j + 1) _ rs t'
      (fun k hk hk' ↦ hdrop k (by omega) (by omega)) ht'
    rcases r with ⟨wire, chal⟩
    simp only [roundsWire, roundsCons, roundTr, FullTranscript.append_fst,
      FullTranscript.append_snd, msgTr_zero, chalTr_zero, ih]
    rw [polyWire, ← hdrop j le_rfl (by omega)]
    exact congrArg (fun x ↦ (⟨x, chal⟩ : Round) :: rs) (RoundPoly.encode_decode hq)

end Compile

end
end LeanerVM.Protocol
