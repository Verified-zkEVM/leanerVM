/-
  LeanVM.E2E.Termination2

  Termination (T3) from two challenges: on a log without failure and without a prediction of a
  batching's last TWO matrix challenges by one statement input, a child's statement digest is
  answered before its parent's, and the game ends with such a prediction with probability at most
  `(Q³ - Q) / (6 · 2^384) ≤ Q³ / (6 · 2^384)`.
-/

module

public import LeanVM.E2E.Termination

/-!
# Termination from two challenges (T3, cubic)

`LeanVM.E2E.Termination` excludes `Pred o ℓ`: an input carrying, at the offset `o` of the
parent's last matrix coordinate, the challenge of an answer of the same or a later entry. Its
probability is a birthday bound, `Q (Q + 1) / 2^193`.

**Two coordinates.** The parent's statement bytes carry its whole deferred matrix point, the
challenges of the matrices' sumcheck, at consecutive 24-byte cells (`slice_stmtInput_cell`). The
last two, at the offsets `o - 24` and `o`, are the challenges of two consecutive rounds: the
round of the last one is chained after the state of the second-to-last one
(`split_batchRoundsWith`, `chainLT_batchRoundsWith`), and that state comes after every child's
digest (`absorbed_obsAllW_children`). So if the parent's statement entry came no later than
the second-to-last challenge's entry, its input would predict both challenges.

**The event** (`Pred2V V o₁ o₂ ℓ`): entries `j ≤ i₁ < i₂`, all three inputs in `V`, the input
of `j` carrying at `o₁` the challenge of the answer of `i₁` and at `o₂` the one of `i₂`.
`Pred2 = Pred2V True` is the plain form; `Vis/Pred2.lean` restricts it to non-hidden entries.
Every `Pred2` is a `Pred` at `o₂` (`pred_of_pred2V`).

**T3 from it** (`rank_lt_of_child2`): with at least two matrix coordinates (two at the guest's
shape, `2 · blake2sR1csLogSize`), without failure and without `Pred2 (o - 24) o`, a child's
digest is answered before its parent's.

**The probability** (`prEvent_game_pred2_le`). The potential is
`ind Pred2V + H(ℓ) · m / 2^192 + B(c, m) / 2^384`, with `m` the fresh answers still to come,
`H(ℓ)` the number of inputs whose `o₁`-slice is already the challenge of the same or a later
answer (a *half match*), `c` the number of entries and `B c 0 = 0`,
`B c (m + 1) = (c + 1) m + B (c + 1) m` (`budget2`). A fresh answer completes a half match with
probability at most `H / |E|` and makes a new one with probability at most `(c + 1) / |E|`
(`pot2_step`); on the empty log the potential is `B 0 Q / 2^384 = (Q³ - Q) / (6 · 2^384)`.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Rom
open LeanVM.Node LeanVM.Guest.Batch OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/- `E`'s enumeration is the repository's (`sum_challengeOf_div`), not leanDA's. -/
attribute [local instance 1100] LeanVM.Parameters.instFintypeK

/-! ## Strict order along a chain -/

section Chain

variable {X : Type} {σ : Seeds X} {ℓ : Log}

/-- **`b` strictly follows `a` on the log `ℓ`**: `b` is the answer of an entry after every entry
answering `a`. -/
def ChainLT (ℓ : Log) (a b : Digest) : Prop :=
  ∃ (k : ℕ) (hk : k < ℓ.length), ℓ[k].2 = b ∧ ∀ (i : ℕ) (hi : i < ℓ.length), ℓ[i].2 = a → i < k

/-- Strictly following, then following, is strictly following. -/
theorem ChainLT.trans_le {a b c : Digest} (h₁ : ChainLT ℓ a b) (h₂ : ChainLE ℓ b c) :
    ChainLT ℓ a c := by
  obtain ⟨k, hk, hb, h₁⟩ := h₁
  rcases h₂ with rfl | ⟨j, hj, hc, h₂⟩
  · exact ⟨k, hk, hb, h₁⟩
  · exact ⟨j, hj, hc, fun i hi ha ↦ (h₁ i hi ha).trans (h₂ k hk hb)⟩

/-- **A nonempty sumcheck ends strictly after its start.** -/
theorem chainLT_batchRoundsWith (hf : ¬ Fail σ ℓ) :
    ∀ (rounds : List (E × E)) (claim : E) (cv : Digest) {r : (List E × E) × Digest},
      (batchRoundsWith (look ℓ) claim rounds).run cv = some r → rounds ≠ [] → ChainLT ℓ cv r.2
  | [], _, _, _, _, hne => absurd rfl hne
  | (g1, gInf) :: rounds, claim, cv, r, h, _ => by
    rw [batchRoundsWith_run_cons, Option.bind_eq_some_iff] at h
    obtain ⟨c1, h1, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨c2, h2, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨c3, h3, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    obtain ⟨j, hj, hej, -, hlt⟩ := chain_step hf h1
    exact (ChainLT.trans_le ⟨j, hj, by rw [hej], hlt⟩
      (((chainLE_step hf h2).trans (chainLE_step hf h3)).trans
        (chainLE_batchRoundsWith hf rounds _ c3 (r := r') hr')))

end Chain

/-! ## A sumcheck's last round -/

section Split

variable {H : Bytes → Option Digest}

/-- **A sumcheck over concatenated rounds** runs the first rounds, then the rest from the claim
and the state they end at. -/
theorem batchRoundsWith_run_append :
    ∀ (a b : List (E × E)) (claim : E) (cv : Digest),
      (batchRoundsWith H claim (a ++ b)).run cv =
        ((batchRoundsWith H claim a).run cv).bind fun r ↦
          ((batchRoundsWith H r.1.2 b).run r.2).map fun r' ↦ ((r.1.1 ++ r'.1.1, r'.1.2), r'.2)
  | [], b, claim, cv => by
    simp only [List.nil_append, batchRoundsWith, StateT.run_pure, Option.pure_def,
      Option.bind_some]
    rcases (batchRoundsWith H claim b).run cv with _ | r'
    · rfl
    · rfl
  | (g1, gInf) :: a, b, claim, cv => by
    rw [List.cons_append, batchRoundsWith_run_cons, batchRoundsWith_run_cons]
    rcases H (digestBytes cv ++ blockOf g1 1) with _ | c1
    · rfl
    simp only [Option.bind_some]
    rcases H (digestBytes c1 ++ blockOf gInf 1) with _ | c2
    · rfl
    simp only [Option.bind_some]
    rcases H (digestBytes c2 ++ blockOf 0 2) with _ | c3
    · rfl
    simp only [Option.bind_some]
    rw [batchRoundsWith_run_append a b]
    rcases (batchRoundsWith H (roundPoly claim (g1, gInf) (challengeOf c3)) a).run c3 with _ | r
    · rfl
    · simp only [Option.bind_some, Option.map_some]
      rcases (batchRoundsWith H r.1.2 b).run r.2 with _ | r'
      · rfl
      · rfl

/-- **The last round of a sumcheck of at least two rounds**: the rounds before it, nonempty, end
at a state `cvp` whose challenge is the second-to-last one; the last round runs from `cvp` to the
final state, whose challenge is the last one. -/
theorem split_batchRoundsWith {rounds : List (E × E)} {claim : E} {cv : Digest} {rs : List E}
    {fin : E} {cv' : Digest} (h : (batchRoundsWith H claim rounds).run cv = some ((rs, fin), cv'))
    (h2 : 2 ≤ rounds.length) :
    ∃ (pre : List (E × E)) (rd : E × E) (rs' : List E) (claim' : E) (cvp : Digest),
      pre ≠ [] ∧ (batchRoundsWith H claim pre).run cv = some ((rs', claim'), cvp) ∧
      (batchRoundsWith H claim' [rd]).run cvp = some (([challengeOf cv'], fin), cv') ∧
      rs = rs' ++ [challengeOf cv'] ∧ rs'.getLast? = some (challengeOf cvp) := by
  have hne : rounds ≠ [] := by rintro rfl; simp at h2
  have e : rounds = rounds.dropLast ++ [rounds.getLast hne] :=
    (List.dropLast_append_getLast hne).symm
  have hpre : rounds.dropLast ≠ [] := by
    intro he
    have := congrArg List.length he
    simp only [List.length_dropLast, List.length_nil] at this
    omega
  rw [e, batchRoundsWith_run_append, Option.bind_eq_some_iff] at h
  obtain ⟨⟨⟨rs', claim'⟩, cvp⟩, hp, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨⟨rl, fl⟩, cvl⟩, hl, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
  have hlast := getLast_batchRoundsWith _ _ _ hl (List.cons_ne_nil _ _)
  have hlen := length_batchRoundsWith H _ _ _ hl
  obtain ⟨x, rfl⟩ : ∃ x, rl = [x] := List.length_eq_one_iff.mp (by simpa using hlen)
  simp only [List.getLast?_singleton, Option.some.injEq] at hlast
  subst hlast
  exact ⟨_, _, rs', claim', cvp, hpre, hp, hl, rfl, getLast_batchRoundsWith _ _ _ hp hpre⟩

end Split

/-! ## The statement's cells -/

section Statement

/-- **A cell of the statement's bytes**: the 24 bytes at offset `96 + 24 k` are cell `k`'s
encoding. -/
theorem slice_stmtInput_cell (seed sd dd : Digest) (d : DeferredClaim) {k : ℕ}
    (hk : k < d.cells.length) :
    ((stmtInput seed sd dd d).drop (96 + 24 * k)).take 24 = eBytes d.cells[k] := by
  set pad : List E := if d.cells.length % 2 = 1 then [0] else []
  have hk' : k < (d.cells ++ pad).length := by rw [List.length_append]; omega
  have hget : (d.cells ++ pad)[k] = d.cells[k] := List.getElem_append_left hk
  have e : stmtInput seed sd dd d = (digestBytes seed ++ digestBytes sd ++ digestBytes dd) ++
      ((d.cells ++ pad).flatMap eBytes ++ List.replicate
        ((64 - (digestBytes seed ++ digestBytes sd ++ digestBytes dd ++
          (d.cells ++ pad).flatMap eBytes).length % 64) % 64) 0) := by
    simp only [stmtInput, pad, List.append_assoc]
  rw [e, show 96 = (digestBytes seed ++ digestBytes sd ++ digestBytes dd).length by
    simp [digestBytes_length], slice_flatMap_eBytes _ _ hk', hget]

/-- **The last two matrix coordinates in the statement's bytes**: for a matrix point ending
`…, y, x`, the 24 bytes at `96 + 24 (|bytecode point| + |matrix point|) - 24` encode `y`, those
24 bytes later `x`. -/
theorem slice_stmtInput_two (seed sd dd : Digest) {d : DeferredClaim} {ys : List E} {y x : E}
    (hm : d.matrixPoint = ys ++ [y, x]) :
    ((stmtInput seed sd dd d).drop
      (96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length) - 24)).take 24 = eBytes y ∧
    ((stmtInput seed sd dd d).drop
      (96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length))).take 24 = eBytes x := by
  have hcells : d.cells = (d.bytecodePoint ++ [d.bytecodeValue] ++ ys) ++
      (y :: x :: [d.matrixA, d.matrixB]) := by
    simp [DeferredClaim.cells, hm]
  have hlen : d.cells.length = d.bytecodePoint.length + 1 + ys.length + 4 := by
    rw [hcells]; simp; omega
  have hml : d.matrixPoint.length = ys.length + 2 := by rw [hm]; simp
  have e1 : 96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length) - 24 =
      96 + 24 * (d.bytecodePoint.length + 1 + ys.length) := by rw [hml]; omega
  have e2 : 96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length) =
      96 + 24 * (d.bytecodePoint.length + 1 + ys.length + 1) := by rw [hml]; omega
  rw [e1, e2, slice_stmtInput_cell seed sd dd d (by omega),
    slice_stmtInput_cell seed sd dd d (by omega)]
  have g1 : d.cells[d.bytecodePoint.length + 1 + ys.length]'(by omega) = y := by
    simp only [hcells]
    rw [List.getElem_append_right (by simp; omega)]
    have h0 : d.bytecodePoint.length + 1 + ys.length -
        (d.bytecodePoint ++ [d.bytecodeValue] ++ ys).length = 0 := by simp; omega
    simp only [h0]
    rfl
  have g2 : d.cells[d.bytecodePoint.length + 1 + ys.length + 1]'(by omega) = x := by
    simp only [hcells]
    rw [List.getElem_append_right (by simp; omega)]
    have h1 : d.bytecodePoint.length + 1 + ys.length + 1 -
        (d.bytecodePoint ++ [d.bytecodeValue] ++ ys).length = 1 := by simp; omega
    simp only [h1]
    rfl
  rw [g1, g2]
  exact ⟨rfl, rfl⟩

end Statement

/-! ## The two-challenge prediction event and the rank -/

section Rank

variable {X : Type} {σ : Seeds X} {ℓ : Log}

/-- **The two-challenge prediction event, restricted to inputs in `V`**: entries `j ≤ i₁ < i₂`,
all three inputs in `V`, the input of `j` carrying at the offset `o₁` the 24 bytes of the
challenge of the answer of `i₁`, and at `o₂` those of the answer of `i₂`. -/
def Pred2V (V : Bytes → Prop) (o₁ o₂ : ℕ) (ℓ : Log) : Prop :=
  ∃ (i₂ : ℕ) (h₂ : i₂ < ℓ.length) (i₁ : ℕ) (h₁ : i₁ < i₂) (j : ℕ) (hj : j ≤ i₁),
    V (ℓ[j]'(by omega)).1 ∧ V (ℓ[i₁]'(by omega)).1 ∧ V ℓ[i₂].1 ∧
    (((ℓ[j]'(by omega)).1.drop o₁).take 24 = eBytes (challengeOf (ℓ[i₁]'(by omega)).2)) ∧
    (((ℓ[j]'(by omega)).1.drop o₂).take 24 = eBytes (challengeOf ℓ[i₂].2))

/-- **The two-challenge prediction event**: some input carries at `o₁` the challenge of the
answer of the same or a later entry `i₁`, and at `o₂` the challenge of the answer of an entry
after `i₁`. -/
def Pred2 (o₁ o₂ : ℕ) (ℓ : Log) : Prop := Pred2V (fun _ ↦ True) o₁ o₂ ℓ

/-- **A two-challenge prediction is a prediction** at its second offset. -/
theorem pred_of_pred2V {V : Bytes → Prop} {o₁ o₂ : ℕ} (h : Pred2V V o₁ o₂ ℓ) : Pred o₂ ℓ := by
  obtain ⟨i₂, h₂, i₁, h₁, j, hj, -, -, -, -, heq⟩ := h
  exact ⟨i₂, h₂, j, by omega, heq⟩

/-- **T3 from two challenges, the cache form**: `rank_lt_of_child` with at least two matrix
coordinates and `Pred2` at the offsets of the last two for `Pred` at the last one. -/
theorem rank_lt_of_child2 (hf : ¬ Fail σ ℓ) {seed sd dd pi : Digest} {d : DeferredClaim}
    (hP : ¬ Pred2 (96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length) - 24)
      (96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length)) ℓ)
    (hpi : look ℓ (stmtInput seed sd dd d) = some pi) (hm : 2 ≤ d.matrixPoint.length)
    {s0 : Digest} {cs : List ChildClaims} {h : BatchHints}
    (hbw : batchWith (look ℓ) s0 cs h = some (some d)) {c : ChildClaims} (hc : c ∈ cs)
    {i p : ℕ} (hi : i < ℓ.length) (hp : p < ℓ.length) (hci : ℓ[i].2 = c.publicInput)
    (hpp : ℓ[p].2 = pi) : i < p := by
  obtain ⟨cvA, lB, cv1, rB, fB, cv2, lM, cv3, cM, fM, cv4, hA, h1, h2, h3, h4⟩ :=
    batchWith_some_full hbw
  rw [obsAllW_cons, Option.bind_eq_some_iff] at hA
  obtain ⟨cv0, -, hA⟩ := hA
  have hab := absorbed_obsAllW_children hf cs cv0 cvA hA c hc ⟨i, hi, hci⟩
  have hc3 : ChainLE ℓ cvA cv3 :=
    ((chainLE_sq2W hf _ _ h1).trans (chainLE_batchRoundsWith hf _ _ _ h2)).trans
      (chainLE_sq3W hf _ _ h3)
  have hlen := length_batchRoundsWith (look ℓ) _ _ _ h4
  obtain ⟨pre, rd, rs', claim', cvp, hpre, hrp, hrl, hrs, hlast⟩ :=
    split_batchRoundsWith h4 (by omega)
  have hcp : ChainLE ℓ cv3 cvp := chainLE_batchRoundsWith hf _ _ _ hrp
  obtain ⟨i', k₁, hi', hk₁, hci', hik, hck₁⟩ := ((hab.chain hc3).chain hcp).exists_lt
  obtain rfl : i' = i := index_eq_of_output hf hi' hi (by rw [hci', hci])
  obtain ⟨k₂, hk₂, hck₂, hlt⟩ := chainLT_batchRoundsWith hf _ _ _ hrl (List.cons_ne_nil _ _)
  have hk : k₁ < k₂ := hlt k₁ hk₁ hck₁
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  have hmp : d.matrixPoint = ys ++ [challengeOf cvp, challengeOf cv4] := by
    rw [hrs, hys]; simp
  obtain ⟨hs1, hs2⟩ := slice_stmtInput_two seed sd dd hmp
  obtain ⟨p', hp', hep, -⟩ := (look_eq_some_iff ℓ _ _).mp hpi
  obtain rfl : p' = p := index_eq_of_output hf hp' hp (by rw [hep, hpp])
  have hkp : k₁ < p' := by
    by_contra hle
    refine hP ⟨k₂, hk₂, k₁, hk, p', by omega, trivial, trivial, trivial, ?_, ?_⟩
    · rw [hep, hck₁]; exact hs1
    · rw [hep, hck₂]; exact hs2
  omega

end Rank

/-! ## The probability of a two-challenge prediction -/

section Prob

variable {V : Bytes → Prop} {o₁ o₂ : ℕ}

/-- The inputs of the log `ℓ` followed by `t`, by position (`[]` past the end). -/
def inpOf (ℓ : Log) (t : Bytes) (j : ℕ) : Bytes := (ℓ.map Prod.fst ++ [t]).getD j []

/-- An entry's input, in a log with one more entry. -/
theorem getElem_append_fst {ℓ : Log} {t : Bytes} {u : Digest} {j : ℕ}
    (hj : j < (ℓ ++ [(t, u)]).length) : (ℓ ++ [(t, u)])[j].1 = inpOf ℓ t j := by
  simp only [List.length_append, List.length_singleton] at hj
  unfold inpOf
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  by_cases h : j < ℓ.length
  · rw [List.getElem_append_left h, List.getElem_append_left (by simpa using h)]
    simp
  · obtain rfl : j = ℓ.length := by omega
    rw [List.getElem_append_right (le_refl _), List.getElem_append_right (by simp)]
    simp

/-- The new entry's answer. -/
theorem getElem_append_last_snd {ℓ : Log} {t : Bytes} {u : Digest}
    (h : ℓ.length < (ℓ ++ [(t, u)]).length) : (ℓ ++ [(t, u)])[ℓ.length].2 = u := by
  rw [List.getElem_append_right (le_refl _)]
  simp

/-- The indicator of a conjunction is the product. -/
theorem ind_and (p q : Prop) : ind (p ∧ q) = ind p * ind q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [ind, hp, hq]

/-- An indicator of an existential over a finite set is at most the sum of the indicators. -/
theorem ind_exists_finset_le_nat (s : Finset ℕ) (q : ℕ → Prop) :
    ind (∃ j ∈ s, q j) ≤ ∑ j ∈ s, ind (q j) := by
  by_cases h : ∃ j ∈ s, q j
  · obtain ⟨j, hj, hq⟩ := h
    rw [ind_of ⟨j, hj, hq⟩]
    calc (1 : ℝ≥0∞) = ind (q j) := (ind_of hq).symm
      _ ≤ _ := Finset.single_le_sum (f := fun j ↦ ind (q j)) (fun _ _ ↦ bot_le) hj
  · rw [ind_of_not h]; exact bot_le

/-- **A half match at `j`**: entry `j`'s input, in `V`, carries at `o₁` the 24 bytes of the
challenge of the answer of the same or a later entry with input in `V`. -/
def HalfV (V : Bytes → Prop) (o₁ : ℕ) (ℓ : Log) (j : ℕ) : Prop :=
  ∃ (hj : j < ℓ.length) (i₁ : ℕ) (hi : i₁ < ℓ.length), j ≤ i₁ ∧ V ℓ[j].1 ∧ V ℓ[i₁].1 ∧
    (ℓ[j].1.drop o₁).take 24 = eBytes (challengeOf ℓ[i₁].2)

/-- **The number of half matches.** -/
noncomputable def halfCount (V : Bytes → Prop) (o₁ : ℕ) (ℓ : Log) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range ℓ.length, ind (HalfV V o₁ ℓ j)

open Classical in
/-- **The number of entries with input in `V`.** -/
noncomputable def visCount (V : Bytes → Prop) (ℓ : Log) : ℕ :=
  ((ℓ.map Prod.fst).filter fun x ↦ decide (V x)).length

/-- **The potential's budget** `B c m` for `m` more answers after `c`: `B c 0 = 0`,
`B c (m + 1) = (c + 1) m + B (c + 1) m`, so `B c m = Σ_{c ≤ k < c + m} (k + 1)(c + m - 1 - k)`. -/
def budget2 : ℕ → ℕ → ℕ
  | _, 0 => 0
  | c, m + 1 => (c + 1) * m + budget2 (c + 1) m

/-- **The two-challenge prediction's potential** for `m` more answers: the indicator, the half
matches times `m / |E|`, and the budget `B (c, m) / |E|²`, `c` the entries with input in `V`. -/
noncomputable def pot2 (V : Bytes → Prop) (o₁ o₂ m : ℕ) (ℓ : Log) : ℝ≥0∞ :=
  ind (Pred2V V o₁ o₂ ℓ) + halfCount V o₁ ℓ * (m * ((2 : ℝ≥0∞) ^ 192)⁻¹) +
    (budget2 (visCount V ℓ) m : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 192)⁻¹ ^ 2

/-- A two-challenge prediction in a log with one more entry is one in the log, or the new entry
is in `V` and its answer's challenge is the `o₂`-slice of a half-matched input. -/
theorem pred2V_append {ℓ : Log} {t : Bytes} {u : Digest} (h : Pred2V V o₁ o₂ (ℓ ++ [(t, u)])) :
    Pred2V V o₁ o₂ ℓ ∨ (V t ∧ ∃ j ∈ Finset.range ℓ.length, HalfV V o₁ ℓ j ∧
      ((inpOf ℓ t j).drop o₂).take 24 = eBytes (challengeOf u)) := by
  obtain ⟨i₂, h₂, i₁, h₁, j, hj, vj, vi, v₂, s1, s2⟩ := h
  simp only [List.length_append, List.length_singleton] at h₂
  have hi₁ : i₁ < ℓ.length := by omega
  have hj' : j < ℓ.length := by omega
  rw [List.getElem_append_left hj'] at vj s1 s2
  rw [List.getElem_append_left hi₁] at vi s1
  by_cases hil : i₂ < ℓ.length
  · rw [List.getElem_append_left hil] at v₂ s2
    exact Or.inl ⟨i₂, hil, i₁, h₁, j, hj, vj, vi, v₂, s1, s2⟩
  · obtain rfl : i₂ = ℓ.length := by omega
    rw [List.getElem_append_right (le_refl _)] at v₂ s2
    simp only [Nat.sub_self, List.getElem_singleton] at v₂ s2
    refine Or.inr ⟨v₂, j, Finset.mem_range.mpr hj', ⟨hj', i₁, hi₁, hj, vj, vi, s1⟩, ?_⟩
    have e := getElem_append_fst (ℓ := ℓ) (t := t) (u := u) (j := j) (by simp; omega)
    rw [List.getElem_append_left hj'] at e
    rw [← e]
    exact s2

/-- A two-challenge prediction stays one in a longer log. -/
theorem pred2V_append_of {ℓ : Log} {e : Bytes × Digest} (h : Pred2V V o₁ o₂ ℓ) :
    Pred2V V o₁ o₂ (ℓ ++ [e]) := by
  obtain ⟨i₂, h₂, i₁, h₁, j, hj, vj, vi, v₂, s1, s2⟩ := h
  have hi₁ : i₁ < ℓ.length := by omega
  have hj' : j < ℓ.length := by omega
  refine ⟨i₂, by simp; omega, i₁, h₁, j, hj, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [List.getElem_append_left hj']
  · rwa [List.getElem_append_left hi₁]
  · rwa [List.getElem_append_left h₂]
  · rwa [List.getElem_append_left hj', List.getElem_append_left hi₁]
  · rwa [List.getElem_append_left hj', List.getElem_append_left h₂]

/-- A half match in a log with one more entry is one in the log, or the new entry is in `V` and
its answer's challenge is the `o₁`-slice of an input in `V`. -/
theorem halfV_append {ℓ : Log} {t : Bytes} {u : Digest} {j : ℕ}
    (h : HalfV V o₁ (ℓ ++ [(t, u)]) j) :
    HalfV V o₁ ℓ j ∨ (V t ∧ V (inpOf ℓ t j) ∧
      ((inpOf ℓ t j).drop o₁).take 24 = eBytes (challengeOf u)) := by
  obtain ⟨hj, i₁, hi, hji, vj, vi, s⟩ := h
  have ej := getElem_append_fst hj
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hil : i₁ < ℓ.length
  · have hj' : j < ℓ.length := by omega
    rw [List.getElem_append_left hj'] at vj s
    rw [List.getElem_append_left hil] at vi s
    exact Or.inl ⟨hj', i₁, hil, hji, vj, vi, s⟩
  · obtain rfl : i₁ = ℓ.length := by omega
    rw [List.getElem_append_right (le_refl _)] at vi s
    simp only [Nat.sub_self, List.getElem_singleton] at vi s
    rw [ej] at vj s
    exact Or.inr ⟨vi, vj, s⟩

/-- No half match at or past the end. -/
theorem not_halfV_of_le {ℓ : Log} {j : ℕ} (h : ℓ.length ≤ j) : ¬ HalfV V o₁ ℓ j :=
  fun ⟨hj, _⟩ ↦ by omega

/-- **The half matches of a log with one more entry**: those of the log, and, if the new entry is
in `V`, the inputs in `V` whose `o₁`-slice is its answer's challenge. -/
theorem halfCount_append_le (ℓ : Log) (t : Bytes) (u : Digest) :
    halfCount V o₁ (ℓ ++ [(t, u)]) ≤ halfCount V o₁ ℓ + ind (V t) *
      ∑ j ∈ Finset.range (ℓ.length + 1), ind (V (inpOf ℓ t j)) *
        ind (((inpOf ℓ t j).drop o₁).take 24 = eBytes (challengeOf u)) := by
  unfold halfCount
  rw [List.length_append, List.length_singleton, Finset.mul_sum]
  have hl : ∑ j ∈ Finset.range ℓ.length, ind (HalfV V o₁ ℓ j) =
      ∑ j ∈ Finset.range (ℓ.length + 1), ind (HalfV V o₁ ℓ j) := by
    rw [Finset.sum_range_succ, ind_of_not (not_halfV_of_le le_rfl), add_zero]
  rw [hl, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  refine (ind_mono halfV_append).trans ((ind_or_le _ _).trans (add_le_add le_rfl (le_of_eq ?_)))
  rw [ind_and, ind_and]

/-- **A two-challenge prediction in a log with one more entry**, in indicators. -/
theorem ind_pred2V_append_le (ℓ : Log) (t : Bytes) (u : Digest) :
    ind (Pred2V V o₁ o₂ (ℓ ++ [(t, u)])) ≤ ind (Pred2V V o₁ o₂ ℓ) + ind (V t) *
      ∑ j ∈ Finset.range ℓ.length, ind (HalfV V o₁ ℓ j) *
        ind (((inpOf ℓ t j).drop o₂).take 24 = eBytes (challengeOf u)) := by
  refine (ind_mono pred2V_append).trans ((ind_or_le _ _).trans (add_le_add le_rfl ?_))
  rw [ind_and]
  refine mul_le_mul' le_rfl ((ind_exists_finset_le_nat _ _).trans (le_of_eq ?_))
  exact Finset.sum_congr rfl fun j _ ↦ ind_and _ _

/-- **A fresh answer's challenge is a given slice** with probability at most `1/|E|`, weighted
over a finite set of slices. -/
theorem avg_sum_predicts (o : ℕ) (s : Finset ℕ) (g : ℕ → Bytes) (w : ℕ → ℝ≥0∞) :
    (∑ u : Digest, ∑ j ∈ s, w j * ind (((g j).drop o).take 24 = eBytes (challengeOf u))) /
      Fintype.card Digest ≤ (∑ j ∈ s, w j) * ((2 : ℝ≥0∞) ^ 192)⁻¹ := by
  rw [Finset.sum_comm, div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [← Finset.mul_sum, mul_assoc]
  refine mul_le_mul' le_rfl ?_
  have h := avg_ind_predicts o [g j]
  simp only [List.mem_singleton, exists_eq_left, List.length_singleton, Nat.cast_one,
    one_div] at h
  rwa [div_eq_mul_inv] at h

open Classical in
/-- The inputs in `V`, by position, counted. -/
theorem sum_ind_getD (L : List Bytes) :
    ∑ j ∈ Finset.range L.length, ind (V (L.getD j [])) =
      ((L.filter fun x ↦ decide (V x)).length : ℝ≥0∞) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.filter_cons]
    by_cases ha : V a
    · simp [ha, ind]
    · simp [ha, ind]

open Classical in
/-- **The inputs of the log and a new one in `V`**: the log's count, and one. -/
theorem sum_ind_inpOf (ℓ : Log) {t : Bytes} (ht : V t) :
    ∑ j ∈ Finset.range (ℓ.length + 1), ind (V (inpOf ℓ t j)) = (visCount V ℓ + 1 : ℕ) := by
  have h := sum_ind_getD (V := V) (ℓ.map Prod.fst ++ [t])
  simp only [List.length_append, List.length_map, List.length_singleton] at h
  unfold inpOf
  rw [h, visCount, List.filter_append]
  simp [ht]

open Classical in
/-- An entry in `V` adds one to the count. -/
theorem visCount_append_of {ℓ : Log} {t : Bytes} (u : Digest) (ht : V t) :
    visCount V (ℓ ++ [(t, u)]) = visCount V ℓ + 1 := by
  simp [visCount, List.filter_append, ht]

open Classical in
/-- An entry outside `V` adds nothing to the count. -/
theorem visCount_append_of_not {ℓ : Log} {t : Bytes} (u : Digest) (ht : ¬ V t) :
    visCount V (ℓ ++ [(t, u)]) = visCount V ℓ := by
  simp [visCount, List.filter_append, ht]

/-- The budget grows with the count. -/
theorem budget2_le_succ_left : ∀ (c m : ℕ), budget2 c m ≤ budget2 (c + 1) m
  | _, 0 => le_rfl
  | c, m + 1 => by
    simp only [budget2]
    have := budget2_le_succ_left (c + 1) m
    have : (c + 1) * m ≤ (c + 1 + 1) * m := Nat.mul_le_mul_right _ (by omega)
    omega

/-- The budget grows with the answers to come. -/
theorem budget2_le_succ (c m : ℕ) : budget2 c m ≤ budget2 c (m + 1) := by
  rw [budget2]
  exact (budget2_le_succ_left c m).trans (Nat.le_add_left _ _)

/-- **The budget in closed form**: `6 B (c, m) + m (m + 3c + 1) = m² (m + 3c + 1)`. -/
theorem budget2_eq : ∀ (c m : ℕ),
    6 * budget2 c m + m * (m + 3 * c + 1) = m * m * (m + 3 * c + 1)
  | _, 0 => by simp [budget2]
  | c, m + 1 => by
    have ih := budget2_eq (c + 1) m
    simp only [budget2]
    nlinarith [ih]

/-- **The budget from the start**: `6 B (0, m) + m = m³`. -/
theorem budget2_zero (m : ℕ) : 6 * budget2 0 m + m = m ^ 3 := by
  have h := budget2_eq 0 m
  simp only [Nat.mul_zero, Nat.add_zero] at h
  nlinarith [h]

/-- `|E|⁻²` is `2^-384`. -/
theorem inv_two_pow_192_sq : ((2 : ℝ≥0∞) ^ 192)⁻¹ ^ 2 = ((2 : ℝ≥0∞) ^ 384)⁻¹ := by
  rw [← ENNReal.inv_pow, ← pow_mul]

/-- **The potential's budget at the start**: `B (0, m) / 2^384 = (m³ - m) / (6 · 2^384)`. -/
theorem budget2_zero_div (m : ℕ) :
    (budget2 0 m : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 192)⁻¹ ^ 2 = ((m ^ 3 - m : ℕ) : ℝ≥0∞) / (6 * 2 ^ 384) := by
  have h := budget2_zero m
  have e : m ^ 3 - m = 6 * budget2 0 m := by omega
  rw [e, inv_two_pow_192_sq, Nat.cast_mul, Nat.cast_ofNat, ENNReal.mul_div_mul_left _ _
    (by norm_num) (by norm_num), div_eq_mul_inv]

/-- **The two-challenge term**: `Q³ / (6 · 2^384)`. -/
noncomputable def predError2 (Q : ℕ) : ℝ≥0∞ := ((Q ^ 3 : ℕ) : ℝ≥0∞) / (6 * 2 ^ 384)

/-- The exact term is at most `Q³ / (6 · 2^384)`. -/
theorem budget2_zero_le (m : ℕ) :
    (budget2 0 m : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 192)⁻¹ ^ 2 ≤ predError2 m := by
  rw [budget2_zero_div, predError2]
  gcongr
  exact Nat.sub_le _ _

/-- The term grows with the queries. -/
theorem predError2_mono {Q Q' : ℕ} (h : Q ≤ Q') : predError2 Q ≤ predError2 Q' := by
  unfold predError2
  gcongr

/-- **T3's term is below a birthday bound over 256 bits** for `Q ≤ 2^128`:
`Q³ / (6 · 2^384) ≤ Q² / 2^256`. -/
theorem predError2_le_sq {Q : ℕ} (hQ : Q ≤ 2 ^ 128) :
    predError2 Q ≤ ((Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have e : (6 * 2 ^ 384 : ℝ≥0∞) = ((6 * 2 ^ 128 : ℕ) : ℝ≥0∞) * 2 ^ 256 := by
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]; rw [mul_assoc, ← pow_add]
  have h : Q ^ 3 ≤ 6 * 2 ^ 128 * Q ^ 2 := by
    rw [pow_succ', mul_comm Q, mul_comm (6 * 2 ^ 128)]
    exact Nat.mul_le_mul_left _ (hQ.trans (by norm_num))
  rw [predError2, e]
  calc ((Q ^ 3 : ℕ) : ℝ≥0∞) / (((6 * 2 ^ 128 : ℕ) : ℝ≥0∞) * 2 ^ 256)
      ≤ ((6 * 2 ^ 128 * Q ^ 2 : ℕ) : ℝ≥0∞) / (((6 * 2 ^ 128 : ℕ) : ℝ≥0∞) * 2 ^ 256) := by
        gcongr
    _ = ((Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
        rw [Nat.cast_mul (6 * 2 ^ 128), ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

/-- T3's term is at most its rounded-up numerator over `2^256`. -/
theorem predError2_le_num (Qv : ℕ) :
    predError2 Qv ≤ ((Qv ^ 3 / (6 * 2 ^ 128) + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have h : Qv ^ 3 ≤ 6 * 2 ^ 128 * (Qv ^ 3 / (6 * 2 ^ 128) + 1) := by
    have := Nat.lt_div_mul_add (a := Qv ^ 3) (b := 6 * 2 ^ 128) (by norm_num)
    rw [mul_add, mul_one, mul_comm]
    omega
  have e : (6 * 2 ^ 384 : ℝ≥0∞) = ((6 * 2 ^ 128 : ℕ) : ℝ≥0∞) * 2 ^ 256 := by
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]; rw [mul_assoc, ← pow_add]
  rw [predError2, e]
  calc ((Qv ^ 3 : ℕ) : ℝ≥0∞) / (((6 * 2 ^ 128 : ℕ) : ℝ≥0∞) * 2 ^ 256)
      ≤ ((6 * 2 ^ 128 * (Qv ^ 3 / (6 * 2 ^ 128) + 1) : ℕ) : ℝ≥0∞) /
          (((6 * 2 ^ 128 : ℕ) : ℝ≥0∞) * 2 ^ 256) := by
        gcongr
    _ = _ := by
        rw [Nat.cast_mul (6 * 2 ^ 128), ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

/-- **A fresh answer of an entry in `V` spends one unit of the potential's budget.** -/
theorem pot2_step {ℓ : Log} {t : Bytes} (ht : V t) (m : ℕ) :
    (∑ u, pot2 V o₁ o₂ m (ℓ ++ [(t, u)])) / Fintype.card Digest ≤ pot2 V o₁ o₂ (m + 1) ℓ := by
  set ε : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 192)⁻¹ with hε
  set H := halfCount V o₁ ℓ
  set c := visCount V ℓ
  set F : Digest → ℝ≥0∞ := fun u ↦ ∑ j ∈ Finset.range ℓ.length, ind (HalfV V o₁ ℓ j) *
    ind (((inpOf ℓ t j).drop o₂).take 24 = eBytes (challengeOf u))
  set G : Digest → ℝ≥0∞ := fun u ↦ ∑ j ∈ Finset.range (ℓ.length + 1), ind (V (inpOf ℓ t j)) *
    ind (((inpOf ℓ t j).drop o₁).take 24 = eBytes (challengeOf u))
  have hpt : ∀ u, pot2 V o₁ o₂ m (ℓ ++ [(t, u)]) ≤
      (ind (Pred2V V o₁ o₂ ℓ) + H * (m * ε) + (budget2 (c + 1) m : ℝ≥0∞) * ε ^ 2) +
        (F u + G u * (m * ε)) := by
    intro u
    have h1 := ind_pred2V_append_le (V := V) (o₁ := o₁) (o₂ := o₂) ℓ t u
    have h2 := halfCount_append_le (V := V) (o₁ := o₁) ℓ t u
    rw [ind_of ht, one_mul] at h1 h2
    rw [pot2, visCount_append_of u ht]
    calc ind (Pred2V V o₁ o₂ (ℓ ++ [(t, u)])) + halfCount V o₁ (ℓ ++ [(t, u)]) * (m * ε) +
          (budget2 (c + 1) m : ℝ≥0∞) * ε ^ 2
        ≤ (ind (Pred2V V o₁ o₂ ℓ) + F u) + (H + G u) * (m * ε) +
          (budget2 (c + 1) m : ℝ≥0∞) * ε ^ 2 := by gcongr
      _ = _ := by ring
  have hF := avg_sum_predicts o₂ (Finset.range ℓ.length) (inpOf ℓ t)
    (fun j ↦ ind (HalfV V o₁ ℓ j))
  have hG := avg_sum_predicts o₁ (Finset.range (ℓ.length + 1)) (inpOf ℓ t)
    (fun j ↦ ind (V (inpOf ℓ t j)))
  rw [sum_ind_inpOf ℓ ht] at hG
  calc (∑ u, pot2 V o₁ o₂ m (ℓ ++ [(t, u)])) / Fintype.card Digest
      ≤ (∑ u, ((ind (Pred2V V o₁ o₂ ℓ) + H * (m * ε) + (budget2 (c + 1) m : ℝ≥0∞) * ε ^ 2) +
          (F u + G u * (m * ε)))) / Fintype.card Digest :=
        ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hpt u) _
    _ = (ind (Pred2V V o₁ o₂ ℓ) + H * (m * ε) + (budget2 (c + 1) m : ℝ≥0∞) * ε ^ 2) +
          ((∑ u, F u) / Fintype.card Digest +
            (∑ u, G u) / Fintype.card Digest * (m * ε)) := by
        rw [avg_const_add, Finset.sum_add_distrib, ENNReal.add_div, ← Finset.sum_mul,
          div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
    _ ≤ (ind (Pred2V V o₁ o₂ ℓ) + H * (m * ε) + (budget2 (c + 1) m : ℝ≥0∞) * ε ^ 2) +
          (H * ε + ((c + 1 : ℕ) : ℝ≥0∞) * ε * (m * ε)) := by
        exact add_le_add le_rfl (add_le_add hF (mul_le_mul' hG le_rfl))
    _ = pot2 V o₁ o₂ (m + 1) ℓ := by
        rw [pot2, budget2]
        push_cast
        ring

/-- **A fresh answer of an entry outside `V` raises nothing.** -/
theorem pot2_le_of_not {ℓ : Log} {t : Bytes} (ht : ¬ V t) (m : ℕ) (u : Digest) :
    pot2 V o₁ o₂ m (ℓ ++ [(t, u)]) ≤ pot2 V o₁ o₂ m ℓ := by
  have h1 := ind_pred2V_append_le (V := V) (o₁ := o₁) (o₂ := o₂) ℓ t u
  have h2 := halfCount_append_le (V := V) (o₁ := o₁) ℓ t u
  rw [ind_of_not ht, zero_mul, add_zero] at h1 h2
  rw [pot2, pot2, visCount_append_of_not u ht]
  gcongr

/-- An entry outside `V` leaves the potential's average unchanged or lower. -/
theorem pot2_step_of_not {ℓ : Log} {t : Bytes} (ht : ¬ V t) (m : ℕ) :
    (∑ u, pot2 V o₁ o₂ m (ℓ ++ [(t, u)])) / Fintype.card Digest ≤ pot2 V o₁ o₂ m ℓ :=
  avg_le_of_le fun u ↦ pot2_le_of_not ht m u

/-- **More answers to come, more potential.** -/
theorem pot2_mono (ℓ : Log) (m : ℕ) : pot2 V o₁ o₂ m ℓ ≤ pot2 V o₁ o₂ (m + 1) ℓ := by
  unfold pot2
  gcongr
  · exact le_self_add
  · exact budget2_le_succ _ _

/-- **On a log without inputs in `V`**, the potential is the budget from the start. -/
theorem pot2_of_none {ℓ : Log} (hall : ∀ e ∈ ℓ, ¬ V e.1) (m : ℕ) :
    pot2 V o₁ o₂ m ℓ = (budget2 0 m : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 192)⁻¹ ^ 2 := by
  classical
  have hP : ¬ Pred2V V o₁ o₂ ℓ := fun ⟨i₂, h₂, _, _, _, _, _, _, v, _⟩ ↦
    hall _ (List.getElem_mem h₂) v
  have hH : halfCount V o₁ ℓ = 0 := by
    refine Finset.sum_eq_zero fun j _ ↦ ind_of_not ?_
    rintro ⟨hj, _, _, _, v, _⟩
    exact hall _ (List.getElem_mem hj) v
  have hc : visCount V ℓ = 0 := by
    simp only [visCount, List.length_eq_zero_iff, List.filter_eq_nil_iff, List.mem_map]
    rintro _ ⟨e, he, rfl⟩
    simpa using hall e he
  rw [pot2, ind_of_not hP, hH, hc, zero_mul, zero_add, zero_add]

/-- **On the empty log**, the potential is the budget from the start. -/
theorem pot2_nil (m : ℕ) :
    pot2 V o₁ o₂ m [] = (budget2 0 m : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 192)⁻¹ ^ 2 :=
  pot2_of_none (fun _ h ↦ absurd h List.not_mem_nil) m

end Prob

/-! ## The game -/

section Game

variable {nx ns : ℕ} [Sphincs.Params]

/-- **T3's probability from two challenges**: the game ends with a two-challenge prediction
(restricted to inputs in any `V`) with probability at most `(Q³ - Q) / (6 · 2^384)`, at any
offsets, for a game with at most `Q` hash queries. -/
theorem prEvent_game_pred2V_le (V : Bytes → Prop) (o₁ o₂ : ℕ) (guest : Semantics.Program)
    (fuel budget : ℕ) (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q) :
    Pr{let z ← game guest fuel budget A}[Pred2V V o₁ o₂ z.2] ≤
      ((Q ^ 3 - Q : ℕ) : ℝ≥0∞) / (6 * 2 ^ 384) := by
  have h := prEvent_game_le_of_freshStepBelow
    (Φ := fun ℓ ↦ pot2 V o₁ o₂ (Q - ℓ.length) ℓ) (δ := 0) Q
    (fun ℓ t hℓ _ ↦ by
      rw [add_zero]
      have e : Q - ℓ.length = (Q - (ℓ.length + 1)) + 1 := by omega
      have e' : ∀ u : Digest, (ℓ ++ [(t, u)]).length = ℓ.length + 1 := fun u ↦ by simp
      simp only [e', e]
      by_cases ht : V t
      · exact pot2_step ht _
      · exact (pot2_step_of_not ht _).trans (pot2_mono ℓ _))
    guest fuel budget A Q hQ le_rfl (fun _ ℓ ↦ Pred2V V o₁ o₂ ℓ) (fun z _ hz ↦ by
      simp only [pot2, ind_of hz]
      exact le_add_right le_self_add)
  simp only [List.length_nil, Nat.sub_zero, pot2_nil, mul_zero, add_zero] at h
  rwa [budget2_zero_div] at h

/-- **T3's probability from two challenges, plain form**: at most `(Q³ - Q) / (6 · 2^384)`. -/
theorem prEvent_game_pred2_le (o₁ o₂ : ℕ) (guest : Semantics.Program) (fuel budget : ℕ)
    (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q) :
    Pr{let z ← game guest fuel budget A}[Pred2 o₁ o₂ z.2] ≤
      ((Q ^ 3 - Q : ℕ) : ℝ≥0∞) / (6 * 2 ^ 384) :=
  prEvent_game_pred2V_le _ o₁ o₂ guest fuel budget A Q hQ

/-- **T3's probability from two challenges, cubic form**: at most `Q³ / (6 · 2^384)`. -/
theorem prEvent_game_pred2_le_cube (o₁ o₂ : ℕ) (guest : Semantics.Program) (fuel budget : ℕ)
    (A : GameAdversary nx ns) (Q : ℕ)
    (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q) :
    Pr{let z ← game guest fuel budget A}[Pred2 o₁ o₂ z.2] ≤ predError2 Q := by
  refine (prEvent_game_pred2_le o₁ o₂ guest fuel budget A Q hQ).trans ?_
  unfold predError2
  gcongr
  exact Nat.sub_le _ _

end Game

end
end LeanVM.E2E
