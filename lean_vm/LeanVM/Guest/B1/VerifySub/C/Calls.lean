/-
  LeanVM.Guest.B1.VerifySub.C.Calls

  `verify_sub`'s calls of the bus's GKR, the tables and the Keccak reduction (G:3241-3253),
  honestly: the statements around the calls, the calls given.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Maps
public import LeanVM.Guest.B1.KeccakGkr.VkStep

/-!
# The three calls, honestly

`vsCallsT_complete`: the GKR cursor (`stream·g^10`), `chi`, `z_vals` and `slices` allocated, the
`KECCAK` table's height read from `dims_g`, the output lanes' pool slot (`claim_pool·g^110`), and
the capacity after `verify_keccak` copied, around the three calls (in `C`, at the honest
valuation's words).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

theorem vsCallsT_noNe : vsCallsT.all noNeB = true := by decide +kernel

theorem vsCalls_notS : Atom.load (.n 858) (.n 129) 6 ∉ vsSL := by decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

set_option maxRecDepth 100000 in
/-- **The three calls' section, honestly.** -/
theorem vsCallsT_complete (hl : args.length = 7) {τg : E}
    (hd6 : LoadHolds rd (vsσ rd w args (.n 129)) 6 τg) {C : CallRel}
    (hCg : C "verify_bus_gkr" ([825, 826, 827, 828, 829, 838, 522, 523].map (vsσ rd w args ∘ V.n))
      ((List.range 9).map (vsσ rd w args ∘ V.n ∘ (839 + ·))))
    (hCt : C "verify_tables" ([839, 840, 841, 842, 843, 844, 0, 1, 523, 522, 129, 28, 149, 5, 640,
      836, 7, 8, 848, 845, 846, 847].map (vsσ rd w args ∘ V.n))
      ((List.range 9).map (vsσ rd w args ∘ V.n ∘ (849 + ·))))
    (hCk : C "verify_keccak" ([849, 850, 851, 852, 853, 854, 858, 848, 862, 859, 860].map
      (vsσ rd w args ∘ V.n)) ((List.range 8).map (vsσ rd w args ∘ V.n ∘ (863 + ·))))
    {next : Prop} {kret : List E → Prop} (hn : next) :
    vsσ rd w args (.n 838) = vsσ rd w args (.n 27) * gen ^ 10 ∧ vsσ rd w args (.n 858) = τg ∧
      vsσ rd w args (.n 862) = vsσ rd w args (.n 7) * gen ^ 110 ∧
      (∀ i < 5, vsσ rd w args (.n (871 + i)) = vsσ rd w args (.n (863 + i))) ∧
      Stmt.HoldsList C rd (vsσ rd w args) vsCallsT next kret := by
  have hG : ∀ s ∈ vsCallsT, GoodS rd vsSL w (vsσ rd w args) s := fun s hs ↦ by
    have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 913) (blk := vsCallsT)
      (by decide +kernel) hs)
    rwa [fixNe_of_noNe (List.all_eq_true.mp vsCallsT_noNe s hs)] at h
  have m : ∀ s, s ∈ [vsConst 837 (word 1024 0 0), vsMul 838 27 837, vsLd 858 129 6,
      vsConst 861 (word 1899956092796928 0 0), vsMul 862 7 861] → s ∈ vsCallsT := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rw [vsCallsT]
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp
  have c837 : vsσ rd w args (.n 837) = word 1024 0 0 := hG (vsConst 837 _) (m _ (by simp))
  have c861 : vsσ rd w args (.n 861) = word 1899956092796928 0 0 := hG (vsConst 861 _) (m _ (by simp))
  have g838 : Good rd vsSL w (vsσ rd w args) (.mul (.n 838) (.n 27) (.n 837)) :=
    hG (vsMul 838 27 837) (m _ (by simp))
  have g862 : Good rd vsSL w (vsσ rd w args) (.mul (.n 862) (.n 7) (.n 861)) :=
    hG (vsMul 862 7 861) (m _ (by simp))
  simp only [Good] at g838 g862
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨show 27 < 838 by norm_num, show 837 < 838 by norm_num⟩)]
    at g838
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨show 7 < 862 by norm_num, show 861 < 862 by norm_num⟩)]
    at g862
  have r858 := good_read (w := w) (hG (vsLd 858 129 6) (m _ (by simp))) vsCalls_notS hd6
  have hcp : ∀ i < 5, vsσ rd w args (.n (871 + i)) = vsσ rd w args (.n (863 + i)) := by
    intro i hi
    have := hG (.atom (.copy (.n (871 + i)) (.n (863 + i)))) (by
      rw [vsCallsT]; exact List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
    exact this
  refine ⟨by rw [g838, c837, show (1024 : ℕ) = 2 ^ 10 from rfl, word_two_pow (by norm_num)],
    r858.1, by rw [g862, c861, show (1899956092796928 : ℕ) = vkGw 5 from rfl,
      vkGw_eq 5 (by norm_num) (by norm_num)], hcp, ?_⟩
  rw [vsCallsT, show List.range 5 = [0, 1, 2, 3, 4] from rfl]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, vsCall, vsConst, vsMul, vsAlloc, vsLd, Atom.Holds]
  refine ⟨c837, g838, ?_, trivial, ?_, r858.2, trivial, trivial, c861, g862, ?_,
    hcp 0 (by norm_num), hcp 1 (by norm_num), hcp 2 (by norm_num), hcp 3 (by norm_num),
    hcp 4 (by norm_num), hn⟩
  · simpa using hCg
  · simpa using hCt
  · simpa using hCk

end
end LeanVM.Guest.B1.VerifySub
