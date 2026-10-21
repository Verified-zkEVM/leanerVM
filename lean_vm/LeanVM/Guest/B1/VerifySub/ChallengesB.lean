/-
  LeanVM.Guest.B1.VerifySub.ChallengesB

  `verify_sub`'s inline challenges under any semantics of `BLAKE2S`: the equality weights of the
  bus's `alpha`s.
-/

module

public import LeanVM.Guest.B1.VerifySub.FrontB
public import LeanVM.Guest.B1.VerifySub.Challenges

/-!
# The bus challenges, under any semantics (G:2137-2153)

`Challenges.lean` over `S : BlakeSem`:

* `vs_fpwB`: `fp_w = eqKernel alphas`, read off runs free of `BLAKE2S` (`vs_fpw`'s proof).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {S : BlakeSem} {rd : Reader} {σ : Val}

/-! ## `fp_w` -/

theorem vs_eqw_blocksF : ∀ x < 16,
    (decide (eqwIdx x + (eqwEntry x (eqwStart x)).1.length ≤ 790) &&
      stmtsEqb (eqwEntry x (eqwStart x)).1
        ((vsPre.drop (eqwIdx x)).take (eqwEntry x (eqwStart x)).1.length) &&
      Stmt.freeInList vsFree (eqwEntry x (eqwStart x)).1) = true := by decide +kernel

/-- **`fp_w` under `S`** (`vs_fpw`): the equality weights of the `alpha`s. -/
theorem vs_fpwB {N : ℕ} (h : VsHoldsToB S N rd σ) (hN : 790 ≤ N) {alphas : List E}
    (hl : alphas.length = 4) (ha : ReadsAt rd (σ (.n 451)) alphas) :
    ReadsAt rd (σ (.n 508)) (eqKernel alphas) := by
  replace h := h.mono hN
  have ha' : ∀ c < 4, ∀ u, LoadHolds rd (σ (.n 451)) c u → u = alphas.getD c 0 := fun c hc u hu => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact loadHolds_unique hu (ha c (by omega))
  obtain ⟨a0, a1, a2, a3, rfl⟩ : ∃ a0 a1 a2 a3, alphas = [a0, a1, a2, a3] := by
    match alphas, hl with
    | [a0, a1, a2, a3], _ => exact ⟨a0, a1, a2, a3, rfl⟩
  intro x hx
  have hlen : (eqKernel [a0, a1, a2, a3]).length = 16 := by simp [eqKernel]
  rw [hlen] at hx
  have := holds_eqwEntry ha' x _ (h.sliceF' _ _ (vs_eqw_blocksF x hx))
  rw [← List.getD_eq_getElem _ 0]
  have e := eqKernel4 (fun c ↦ [a0, a1, a2, a3].getD c 0) x hx
  simp only [List.getD_cons_zero, List.getD_cons_succ] at e
  rw [e]
  exact this

/-! ## Squeezes over a hash model -/

theorem sqAllM_succ' (M : HashModel) : ∀ (n : ℕ) (cv : Digest),
    sqAllM M (n + 1) cv = (sqAllM M n cv).bind fun r ↦
      (sqCvM M r.2).map fun c ↦ (r.1 ++ [challengeOf c], c)
  | 0, cv => by
    cases hc : sqCvM M cv <;> simp [sqAllM, hc]
  | n + 1, cv => by
    rw [show sqAllM M (n + 1 + 1) cv = (sqCvM M cv).bind fun c' ↦
        (sqAllM M (n + 1) c').map fun r ↦ (challengeOf c' :: r.1, r.2) from rfl,
      show sqAllM M (n + 1) cv = (sqCvM M cv).bind fun c' ↦
        (sqAllM M n c').map fun r ↦ (challengeOf c' :: r.1, r.2) from rfl]
    cases sqCvM M cv with
    | none => rfl
    | some c' =>
      simp only [Option.bind_some]
      rw [sqAllM_succ' M n c']
      cases sqAllM M n c' with
      | none => rfl
      | some r =>
        simp only [Option.bind_some, Option.map_map]
        cases h : sqCvM M r.2 <;> simp [h]

theorem sqAllM_length {M : HashModel} : ∀ {n : ℕ} {cv : Digest} {cs : List E} {cv' : Digest},
    sqAllM M n cv = some (cs, cv') → cs.length = n
  | 0, _, _, _, h => by
    simp only [sqAllM, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | n + 1, _, _, _, h => by
    obtain ⟨c, -, hrest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, hrr⟩ := Option.map_eq_some_iff.mp hrest
    simp only [Prod.mk.injEq] at hrr
    rw [← hrr.1, List.length_cons, sqAllM_length hr]

/-- **`m` squeezes over a hash model** (`squeezes`): from the state of `cv`, the `m` challenges
are the model's (`sqAllM`), stored at `out`, and the last state is the model's answer. -/
theorem squeezesM {M : HashModel} {h : VsHoldsB M.sem rd σ} {m s0 : ℕ} {nk st : ℕ → ℕ} {out : V}
    {cv : Digest}
    (hblk : ∀ k < m, stmtsEqb (squeezeT (.n (if k = 0 then s0 else st (k - 1) + 5))
      (.n ((if k = 0 then s0 else st (k - 1) + 5) + 1)) (st k)) ((vsPre.drop (nk k)).take 14)
        = true)
    (hst : ∀ k < m, (stmtsEqb [.atom (.load (.n (st k + 13)) out k)]
      ((vsPre.drop (nk k + 14)).take 1) &&
        Stmt.freeInList vsFree [.atom (.load (.n (st k + 13)) out k)]) = true)
    (h0 : (σ (.n s0), σ (.n (s0 + 1))) = digestScalars cv) (hm : 0 < m) :
    ∃ cs cv', sqAllM M m cv = some (cs, cv') ∧ ReadsAt rd (σ out) cs ∧
      (σ (.n (st (m - 1) + 5)), σ (.n (st (m - 1) + 6))) = digestScalars cv' := by
  have hs : ∀ k < m, ∃ cs c, sqAllM M (k + 1) cv = some (cs, c) ∧
      (∀ i < k + 1, σ (.n (st i + 13)) = cs.getD i 0) ∧
      (σ (.n (st k + 5)), σ (.n (st k + 6))) = digestScalars c := by
    intro k hk
    induction k with
    | zero =>
      obtain ⟨c, d, hc, hd, h5, h13⟩ := h.squeezeM _ _ _ _ (hblk 0 hk)
      simp only [↓reduceIte] at hc
      rw [h0] at hc
      obtain rfl := digestScalars_injective hc
      refine ⟨[challengeOf d], d, by simp [sqAllM, hd], fun i hi => ?_, h5⟩
      obtain rfl : i = 0 := by omega
      exact h13
    | succ k ih =>
      obtain ⟨cs, c, hsq, hcs, hstk⟩ := ih (by omega)
      obtain ⟨c', d, hc, hd, h5, h13⟩ := h.squeezeM _ _ _ _ (hblk (k + 1) hk)
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hc
      rw [hstk] at hc
      obtain rfl := digestScalars_injective hc
      have hl := sqAllM_length hsq
      refine ⟨cs ++ [challengeOf d], d, by rw [sqAllM_succ', hsq]; simp [hd], fun i hi => ?_, h5⟩
      rcases Nat.lt_or_ge i (k + 1) with hi' | hi'
      · rw [hcs i hi', List.getD_append _ _ _ _ (by omega)]
      · obtain rfl : i = k + 1 := by omega
        rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
        exact h13
  obtain ⟨cs, c, hsq, hcs, hlast⟩ := hs (m - 1) (by omega)
  rw [show m - 1 + 1 = m by omega] at hsq hcs
  refine ⟨cs, c, hsq, fun k hk => ?_, hlast⟩
  have hl := sqAllM_length hsq
  have hk' : k < m := by omega
  rw [← List.getD_eq_getElem _ 0, ← hcs k hk']
  exact h.atomF _ _ (hst k hk')

/-! ## The `alpha`s and `beta` -/

/-- **The four `alpha`s over a hash model** (`vs_alphas`). -/
theorem vs_alphasM {M : HashModel} (h : VsHoldsB M.sem rd σ) {cv : Digest}
    (h0 : (σ (.n 447), σ (.n 448)) = digestScalars cv) :
    ∃ alphas cv', sqAllM M 4 cv = some (alphas, cv') ∧ ReadsAt rd (σ (.n 451)) alphas ∧
      (σ (.n 499), σ (.n 500)) = digestScalars cv' :=
  squeezesM (h := h) (m := 4) (s0 := 447) (nk := fun k ↦ 537 + 15 * k)
    (st := fun k ↦ 452 + 14 * k) (out := .n 451) (by decide +kernel) (by decide +kernel) h0
    (by decide)

/-- **`beta` over a hash model** (`vs_beta`): the state and cursor GKR starts from. -/
theorem vs_betaM {M : HashModel} (h : VsHoldsB M.sem rd σ) {cv : Digest}
    (h0 : (σ (.n 499), σ (.n 500)) = digestScalars cv) :
    ∃ d, sqCvM M cv = some d ∧ (σ (.n 690), σ (.n 691)) = digestScalars d ∧
      σ (.n 698) = challengeOf d ∧ σ (.n 700) = σ (.n 14) * gen ^ 10 := by
  obtain ⟨c, d, hc, hd, h5, h13⟩ := h.squeezeM 790 (.n 499) (.n 500) 685 (by decide +kernel)
  rw [h0] at hc
  obtain rfl := digestScalars_injective hc
  have hs := h.sliceF 804 [.atom (.const (.n 699) (word 1024 0 0)),
    .atom (.mul (.n 700) (.n 14) (.n 699))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
  have w10 : word 1024 0 0 = gen ^ 10 := word_two_pow (a := 10) (by decide)
  exact ⟨d, hd, h5, h13, by rw [hs.2, hs.1, w10]⟩

end
end LeanVM.Guest.B1.VerifySub
