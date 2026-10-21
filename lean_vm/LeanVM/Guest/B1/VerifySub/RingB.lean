/-
  LeanVM.Guest.B1.VerifySub.RingB

  `verify_sub`'s ring-switching front under any semantics of `BLAKE2S`: the map's challenges
  over a hash model, the coefficient table `c_table`.
-/

module

public import LeanVM.Guest.B1.VerifySub.ChallengesB
public import LeanVM.Guest.B1.VerifySub.Ring

/-!
# The ring switch's map, under any semantics (G:2170-2193)

`Ring.lean` over `S : BlakeSem`:

* `vs_mapChallengesM`: over a hash model, the six challenges are the model's (`sqAllM`);
* `vs_ctableB`: `c_table` holds `ringCoefficients` of them, read off runs free of `BLAKE2S`
  (`vs_ctable`'s proof).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {S : BlakeSem} {rd : Reader} {σ : Val}

/-- **The ring map's challenges over a hash model** (`vs_mapChallenges`), squeezed from Flock's
final state. -/
theorem vs_mapChallengesM {M : HashModel} (h : VsHoldsB M.sem rd σ) {cv : Digest}
    (h0 : (σ (.n 730), σ (.n 731)) = digestScalars cv) :
    ∃ mcs cv', sqAllM M 6 cv = some (mcs, cv') ∧ ReadsAt rd (σ (.n 732)) mcs ∧
      (σ (.n 810), σ (.n 811)) = digestScalars cv' :=
  squeezesM (h := h) (m := 6) (s0 := 730) (nk := fun k ↦ 825 + 15 * k)
    (st := fun k ↦ 735 + 14 * k) (out := .n 732) (by decide +kernel) (by decide +kernel) h0
    (by decide)

theorem vs_ct_loadsF : ∀ st < 6,
    (stmtsEqb [.atom (.load (.n (ctV st)) (.n 732) st)] ((vsPre.drop (ctN st)).take 1) &&
      Stmt.freeInList vsFree [.atom (.load (.n (ctV st)) (.n 732) st)]) = true := by
  decide +kernel

theorem vs_ct_slotsF : ∀ st < 6, ∀ sl < 2 ^ st, (stmtsEqb (ctSlot st sl)
    ((vsPre.drop (ctN st + 1 + sl * (ctD st + 3))).take (ctD st + 3)) &&
      Stmt.freeInList vsFree (ctSlot st sl)) = true := by
  decide +kernel

/-- **`c_table` under `S`** (`vs_ctable`): the drawn map's coefficients. -/
theorem vs_ctableB (h : VsHoldsB S rd σ) {mcs : List E} (hl : mcs.length = 6)
    (hm : ReadsAt rd (σ (.n 732)) mcs) :
    ∀ k < 64, LoadHolds rd (σ (.n 733)) k ((ringCoefficients mcs).getD k 0) := by
  have h0 := h.sliceF 915 [.atom (.const (.n 819) (word 1 0 0)), .atom (.load (.n 819) (.n 733) 0)]
    (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at h0
  have hmc : ∀ st < 6, σ (.n (ctV st)) = mcs.getD st 0 := fun st hst => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact loadHolds_unique (h.atomF _ _ (vs_ct_loadsF st hst)) (hm st (by omega))
  have hP : ∀ st ≤ 6, ∀ k < 64, k % (64 >>> st) = 0 → LoadHolds rd (σ (.n 733)) k (ctTab mcs st k) := by
    intro st hst
    induction st with
    | zero =>
      intro k hk hk0
      rw [show k = 0 by simp at hk0; omega]
      simp only [ctTab, ↓reduceIte]
      rw [← h0.1]; exact h0.2
    | succ st ih =>
      intro k hk hkd
      obtain ⟨hd0, hd1, hd2, hd3⟩ := ctD_facts st (by omega)
      rw [hd2] at hkd
      simp only [ctTab]
      by_cases hodd : k % (2 * ctD st) = ctD st
      · simp only [hodd, ↓reduceIte]
        set sl := k / (2 * ctD st) with hsl_def
        have hsl : sl < 2 ^ st := by
          rw [hsl_def, Nat.div_lt_iff_lt_mul (by omega), hd3]; exact hk
        have hk' : k = sl * (2 * ctD st) + ctD st := by
          have := Nat.div_add_mod k (2 * ctD st); rw [hodd] at this; rw [hsl_def]; linarith
        have hs := holds_ctSlot st sl (h.sliceF _ _ (by
          rw [ctSlot_length]; exact vs_ct_slotsF st (by omega) _ hsl))
        have hread := ih (by omega) (sl * (2 * ctD st)) (by omega)
          (by rw [hd1]; exact Nat.mul_mod_left _ _)
        rw [show k - ctD st = sl * (2 * ctD st) by omega, ← loadHolds_unique hs.1 hread,
          ← hmc st (by omega), hk']
        exact hs.2
      · simp only [hodd, ↓reduceIte]
        refine ih (by omega) k hk ?_
        rw [hd1]
        have hr : k % (2 * ctD st) % ctD st = 0 := by rw [Nat.mod_mod_of_dvd _ ⟨2, by ring⟩]; exact hkd
        have hlt := Nat.mod_lt k (show 0 < 2 * ctD st by omega)
        obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hr
        rw [hq] at hlt hodd ⊢
        have hq2 : q < 2 := by
          by_contra hq2; exact absurd hlt (not_lt.mpr (by nlinarith))
        interval_cases q
        · simp
        · exact absurd (by ring) hodd
  intro k hk
  rw [← ctTab_six mcs hl k hk]
  exact hP 6 le_rfl k hk (by rw [show 64 >>> 6 = 1 from rfl, Nat.mod_one])

end
end LeanVM.Guest.B1.VerifySub
