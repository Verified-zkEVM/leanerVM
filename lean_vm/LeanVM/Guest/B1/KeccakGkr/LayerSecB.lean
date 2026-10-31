/-
  LeanVM.Guest.B1.KeccakGkr.LayerSecB

  `keccak_layer`'s middle sections (G:2604-2658): the product at `s` (Horner), the pack rounds'
  first record and their loop, and the last record read.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT

/-!
# The pack rounds' records

`hornerT_holds`: the Horner chain is `polyEval` of the product at `s` (V:1998). `packSetupT_holds`:
the first record (`RoundRec`, the capacity after `s`, the cursor past the product, the product at
`s`, the scale `1`), the loop's call and with `odd` the last round's (`LayerW.h0`, `hloop`,
`hoddc`). `lastT_holds`: the record `rounds·y_last` read.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Horner -/

/-- The value after `j` steps of the chain. -/
def hornerV (a : ℕ → ℕ) (b j : ℕ) : ℕ := if j = 0 then a 46 else b + 2 * j - 1

/-- **Horner** (G:2604-2606): the chain's last value is the product at `s`. -/
theorem hornerT_holds {a : ℕ → ℕ} {s b : ℕ} {cs : List E} (hl : cs.length = 47)
    (hc : ∀ k < 47, σ (.n (a k)) = cs.getD k 0) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (hornerT a s b) next kret) :
    σ (.n (b + 91)) = polyEval cs (σ (.n s)) ∧ next := by
  rw [hornerT, holdsList_range_flatten _ _ (fun _ ↦ rfl)] at h
  obtain ⟨hall, hn⟩ := h
  have step : ∀ j ≤ 46, σ (.n (hornerV a b j)) = polyEval (cs.drop (46 - j)) (σ (.n s)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [hornerV, ↓reduceIte]
      rw [hc 46 (by omega), List.drop_eq_getElem_cons (by omega),
        show 46 + 1 = cs.length by omega, List.drop_length]
      simp [polyEval, List.getElem?_eq_getElem (show 46 < cs.length by omega)]
    | succ j ih =>
      intro hj
      have hj' := hall j (by omega)
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hj'
      obtain ⟨e1, e2⟩ := hj'
      have hv : hornerV a b (j + 1) = b + 2 * j + 1 := by simp [hornerV]; omega
      have hp : (if j = 0 then a 46 else b + 2 * j - 1) = hornerV a b j := rfl
      rw [hv, e2, e1, hp, ih (by omega), hc (45 - j) (by omega),
        show 46 - (j + 1) = 45 - j by omega, show 46 - j = 45 - j + 1 by omega,
        List.drop_eq_getElem_cons (i := 45 - j) (show 45 - j < cs.length by omega)]
      simp only [polyEval, List.foldr_cons, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show 45 - j < cs.length by omega), Option.getD_some]
  have := step 46 le_rfl
  rw [show hornerV a b 46 = b + 91 by simp [hornerV]] at this
  exact ⟨by simpa using this, hn⟩

/-! ## The pack rounds' setup -/

theorem gen47 : word 140737488355328 0 0 = gen ^ 47 := by
  rw [show (140737488355328 : ℕ) = 2 ^ 47 from rfl]; exact word_two_pow (by decide)

/-- **The pack rounds' setup** (G:2607-2649): the first record at `rounds` (value `1310`), the loop's
call, and with `odd` the last round's. -/
theorem packSetupT_holds {first odd : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (packSetupT first odd) next kret) :
    LoadHolds rd (σ (.n 11)) 2 (σ (.n 1308)) ∧
      RoundRec rd (σ (.n 1310)) 0 ((cap5 1078).map σ) (σ (.n 7) * gen ^ 47) (σ (.n 1307)) 1 ∧
      IsInK (1 + σ (.n 9)) ∧
      (1 + σ (.n 9) ≠ 0 →
        C (packLoopName first odd) [1, σ (.n 9), σ (.n 1310), σ (.n 1308), σ (.n 1309)] []) ∧
      (odd = 1 → C "keccak_round" [σ (.n 1310) * σ (.n 9), σ (.n 1308) * σ (.n 9) ^ 2,
        σ (.n 1309) * σ (.n 9) ^ 2] []) ∧ next := by
  rw [packSetupT, holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨lpp, -, -, c0, c1, c2, c3, c4, e11, e12, lcur, lclaim, e13, lsc, e14, e15, e16,
    hik, hcall, h⟩ := h
  have e15' : σ (.n 1315) = 1 + σ (.n 9) := by rw [e15, e14, word_one]
  have hrec : RoundRec rd (σ (.n 1310)) 0 ((cap5 1078).map σ) (σ (.n 7) * gen ^ 47)
      (σ (.n 1307)) 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [cap5, List.map_cons, List.map_nil]
      exact capAt_five c0 c1 c2 c3 c4
    · simpa [krCap, e12, e11, gen47] using lcur
    · simpa [krCap] using lclaim
    · simpa [krCap, e13, word_one] using lsc
  refine ⟨lpp, hrec, e15' ▸ hik, fun hne ↦ ?_, ?_⟩
  · have := hcall (by rw [e15']; exact hne)
    rwa [e16, word_one] at this
  · by_cases ho : odd = 1
    · simp only [ho, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
        List.map_nil] at h
      obtain ⟨e17, e18, e19, e20, hc, hn⟩ := h
      refine ⟨fun _ ↦ ?_, hn⟩
      rw [e18, e19, e20, e17] at hc
      simpa [sq] using hc
    · simp only [ho, ↓reduceIte, Stmt.HoldsList] at h
      exact ⟨fun h' ↦ absurd h' ho, h⟩

/-- **The last record** (G:2650-2654): `rounds·y_last` (value `1317 + d`) and its capacity, cursor
and claim. -/
theorem lastT_holds {d : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (lastT d) next kret) :
    σ (.n (d + 1317)) = σ (.n 1310) * σ (.n 10) ∧
      CapAt rd (σ (.n (d + 1317))) 0 krCap ((cap5 (d + 1318)).map σ) ∧
      LoadHolds rd (σ (.n (d + 1317))) (0 + 5 * krCap) (σ (.n (d + 1323))) ∧
      LoadHolds rd (σ (.n (d + 1317))) (0 + 6 * krCap) (σ (.n (d + 1324))) ∧ next := by
  rw [lastT, holdsList_append, holdsList_append, holdsList_map_atoms] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨e, ⟨hc, lcur, lv, -, hn⟩⟩ := h
  refine ⟨e, ?_, by simpa [krCap] using lcur, by simpa [krCap] using lv, hn⟩
  simp only [cap5, List.map_cons, List.map_nil]
  exact capAt_five (by simpa using hc 0 (by omega)) (by simpa [Nat.add_assoc] using hc 1 (by omega))
    (by simpa [Nat.add_assoc] using hc 2 (by omega)) (by simpa [Nat.add_assoc] using hc 3 (by omega))
    (by simpa [Nat.add_assoc] using hc 4 (by omega))

end
end LeanVM.Guest.B1.VerifySub
