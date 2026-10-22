/-
  LeanVM.E2E.Vis.Pred2

  T3 from two challenges, restricted to non-hidden entries: the event `PredS2` asks the
  predicting input and both predicted entries to be outside the hidden class, and it is enough
  for T3's conclusion at the guest's shape (`RankOK2`), given no failure and no format event.
-/

module

public import LeanVM.E2E.Termination2
public import LeanVM.E2E.Vis.Pred

/-!
# T3 from two challenges, restricted (W-vis)

`Vis/Pred.lean` restricts T3's one-challenge event to non-hidden entries (`PredS`, decision
E2E-6); here the two-challenge event of `LeanVM.E2E.Termination2` is restricted the same way:

* `PredS2 keys o₁ o₂ ℓ := Pred2V (¬ Hid keys ·) o₁ o₂ ℓ`: the predicting input and the two
  predicted entries all non-hidden. Every `PredS2` is a `PredS` at `o₂` (`predS_of_predS2`). Its
  potential is `pot2` at `V = ¬ Hid keys`: a hidden fresh query raises nothing
  (`pot2_step_of_not`), a non-hidden one spends one unit (`pot2_step`).
* At the guest's shape the matrix point has `2 · blake2sR1csLogSize = 28 ≥ 2` coordinates
  (`two_le_matrixPoint_of_shaped`), so the offsets are `predOffset - 24` and `predOffset`, bytes
  `1272` and `1296` of the guest's statement input.
* `rank_lt_of_child_vis2`, `rankOK2_of_vis2`: without failure, the format event and `PredS2` at
  those offsets, `RankOK2` holds. The second-to-last and the last challenge are answers of
  non-hidden chain entries (`not_inPfx_batchRoundsWith` on the rounds before the last and on the
  last), and the parent's statement input is not hidden (`not_hid_stmtInput`).
* `rankOK2_of_pred2`: the plain form, without failure and `Pred2`.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Node LeanVM.Guest.Batch

@[expose] public section

/-- **The guest's shape has at least two matrix coordinates**: `2 · blake2sR1csLogSize = 28`. -/
theorem two_le_matrixPoint_of_shaped {bytecode : List K} {d : DeferredClaim}
    (h : d.Shaped bytecode) : 2 ≤ d.matrixPoint.length := by
  rw [h.2]; unfold blake2sR1csLogSize; omega

/-- **The plain two-challenge form of T3 gives `RankOK2`**: no failure and no two-challenge
prediction at the offsets of the guest's last two matrix coordinates. -/
theorem rankOK2_of_pred2 {ℓ : Log} (hf : ¬ Fail leanVmSeeds ℓ)
    (hP : ¬ Pred2 (predOffset (bytecodeWords Guest.guest) - 24)
      (predOffset (bytecodeWords Guest.guest)) ℓ) : RankOK2 ℓ := by
  intro seed sd dd pi d cs h c i p ho hml _ hpi _ hbw hc hi hp hci hpp
  rw [← ho] at hP
  exact rank_lt_of_child2 hf hP hpi (by rw [hml]; unfold blake2sR1csLogSize; omega) hbw hc hi
    hp hci hpp

variable {nx ns : ℕ} [Sphincs.Params]

/-- **The two-challenge prediction event off the hidden class**: a non-hidden input carries at
`o₁` the challenge of the answer of the same or a later non-hidden entry, and at `o₂` the
challenge of the answer of a non-hidden entry after that one. -/
def PredS2 (keys : Keys nx ns) (o₁ o₂ : ℕ) (ℓ : Log) : Prop :=
  Pred2V (fun x ↦ ¬ Hid keys x) o₁ o₂ ℓ

/-- **A restricted two-challenge prediction is a restricted prediction** at its second
offset. -/
theorem predS_of_predS2 {keys : Keys nx ns} {o₁ o₂ : ℕ} {ℓ : Log} (h : PredS2 keys o₁ o₂ ℓ) :
    PredS keys o₂ ℓ := by
  obtain ⟨i₂, h₂, i₁, h₁, j, hj, vj, -, v₂, -, heq⟩ := h
  exact ⟨i₂, h₂, j, by omega, v₂, vj, heq⟩

section Rank

variable {keys : Keys nx ns} {ℓ : Log}

/-- A state a non-hidden entry answers is the answer of a non-hidden entry at an index. -/
theorem VisAns.exists_index {cv : Digest} (h : VisAns keys ℓ cv) :
    ∃ (k : ℕ) (hk : k < ℓ.length), ℓ[k].2 = cv ∧ ¬ Hid keys ℓ[k].1 := by
  obtain ⟨e, he, rfl, hv⟩ := h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  exact ⟨k, hk, rfl, hv⟩

/-- **T3 from two challenges, restricted, the cache form**: `rank_lt_of_child2` with `PredS2`
for `Pred2`, given no format event, a batching start and a seed that are no hidden prefixes. -/
theorem rank_lt_of_child_vis2 {X : Type} {σ : Seeds X} (hf : ¬ Fail σ ℓ)
    (hF : ¬ FormatT keys ℓ) {seed sd dd pi : Digest} {d : DeferredClaim}
    (hseed : ¬ InPfx keys seed)
    (hP : ¬ PredS2 keys (96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length) - 24)
      (96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length)) ℓ)
    (hpi : look ℓ (stmtInput seed sd dd d) = some pi) (hm : 2 ≤ d.matrixPoint.length)
    {s0 : Digest} (hs0 : ¬ InPfx keys s0) {cs : List ChildClaims} {h : BatchHints}
    (hbw : batchWith (look ℓ) s0 cs h = some (some d)) {c : ChildClaims} (hc : c ∈ cs)
    {i p : ℕ} (hi : i < ℓ.length) (hp : p < ℓ.length) (hci : ℓ[i].2 = c.publicInput)
    (hpp : ℓ[p].2 = pi) : i < p := by
  obtain ⟨cvA, lB, cv1, rB, fB, cv2, lM, cv3, cM, fM, cv4, hA, h1, h2, h3, h4⟩ :=
    batchWith_some_full hbw
  have nA := not_inPfx_obsAllW hF _ _ _ hs0 hA
  have n1 := not_inPfx_sq2W hF _ _ nA h1
  have n2 := (not_inPfx_batchRoundsWith hF _ _ _ n1 h2).1
  have n3 := not_inPfx_sq3W hF _ _ n2 h3
  rw [obsAllW_cons, Option.bind_eq_some_iff] at hA
  obtain ⟨cv0, -, hA⟩ := hA
  have hab := absorbed_obsAllW_children hf cs cv0 cvA hA c hc ⟨i, hi, hci⟩
  have hc3 : ChainLE ℓ cvA cv3 :=
    ((chainLE_sq2W hf _ _ h1).trans (chainLE_batchRoundsWith hf _ _ _ h2)).trans
      (chainLE_sq3W hf _ _ h3)
  have hlen := length_batchRoundsWith (look ℓ) _ _ _ h4
  obtain ⟨pre, rd, rs', claim', cvp, hpre, hrp, hrl, hrs, hlast⟩ :=
    split_batchRoundsWith h4 (by omega)
  obtain ⟨ncp, hvcp⟩ := not_inPfx_batchRoundsWith hF _ _ _ n3 hrp
  have hv4 := (not_inPfx_batchRoundsWith hF _ _ _ ncp hrl).2 (List.cons_ne_nil _ _)
  have hcp : ChainLE ℓ cv3 cvp := chainLE_batchRoundsWith hf _ _ _ hrp
  obtain ⟨i', k₁, hi', hk₁, hci', hik, hck₁⟩ := ((hab.chain hc3).chain hcp).exists_lt
  obtain rfl : i' = i := index_eq_of_output hf hi' hi (by rw [hci', hci])
  obtain ⟨k₂, hk₂, hck₂, hlt⟩ := chainLT_batchRoundsWith hf _ _ _ hrl (List.cons_ne_nil _ _)
  have hk : k₁ < k₂ := hlt k₁ hk₁ hck₁
  obtain ⟨k₁', hk₁', hck₁', hv₁⟩ := (hvcp hpre).exists_index
  obtain rfl : k₁' = k₁ := index_eq_of_output hf hk₁' hk₁ (by rw [hck₁', hck₁])
  obtain ⟨k₂', hk₂', hck₂', hv₂⟩ := hv4.exists_index
  obtain rfl : k₂' = k₂ := index_eq_of_output hf hk₂' hk₂ (by rw [hck₂', hck₂])
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  have hmp : d.matrixPoint = ys ++ [challengeOf cvp, challengeOf cv4] := by
    rw [hrs, hys]; simp
  obtain ⟨hs1, hs2⟩ := slice_stmtInput_two seed sd dd hmp
  obtain ⟨p', hp', hep, -⟩ := (look_eq_some_iff ℓ _ _).mp hpi
  obtain rfl : p' = p := index_eq_of_output hf hp' hp (by rw [hep, hpp])
  have hkp : k₁' < p' := by
    by_contra hle
    refine hP ⟨k₂', hk₂', k₁', hk, p', by omega, ?_, hv₁, hv₂, ?_, ?_⟩
    · rw [hep]; exact not_hid_stmtInput hseed
    · rw [hep, hck₁]; exact hs1
    · rw [hep, hck₂]; exact hs2
  omega

/-- **T3 from two challenges, restricted, gives `RankOK2`**: without failure, the format event
and a restricted two-challenge prediction at the offsets of the guest's last two matrix
coordinates. -/
theorem rankOK2_of_vis2 (hf : ¬ Fail leanVmSeeds ℓ) (hF : ¬ FormatT keys ℓ)
    (hP : ¬ PredS2 keys (predOffset (bytecodeWords Guest.guest) - 24)
      (predOffset (bytecodeWords Guest.guest)) ℓ) : RankOK2 ℓ := by
  intro seed sd dd pi d cs h c i p ho hml hs hpi _ hbw hc hi hp hci hpp
  rw [← ho] at hP
  exact rank_lt_of_child_vis2 hf hF (not_inPfx_seed hf hF hs) hP hpi
    (by rw [hml]; unfold blake2sR1csLogSize; omega) (not_inPfx_aggSeedD keys) hbw hc hi hp hci
    hpp

end Rank

end
end LeanVM.E2E
