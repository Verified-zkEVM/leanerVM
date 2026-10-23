/-
  LeanVM.Guest.B1.KeccakGkr.Round

  B1 of `keccak_round`: its core IR computes one equality-mode round of degree two.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Lib

/-!
# `keccak_round` (TRIAGE G #59)

`keccak_round(rd, pp, pt)` (G:2456-2477) is `Data.core11`: it loads the round record's capacity
and cursor, the coordinate `r = pp[0]`, reads `g₁`, `g₂` (`fs_next`, values `10 .. 29`),
squeezes (one `KECCAK` atom, `challenge_from_state` from value `48`), stores the challenge at
`pt`, and writes the next record: the capacity cells `43 .. 47`, the cursor `·g²`, the claim
`(1 + r + c)(claim + (r + c)·g₁ + (r + c²)·g₂)` and the scale `scale·(1 + r + c)`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem find_keccak_round : coreProgram.find? "keccak_round" = some Data.core11 :=
  Program.find?_of_indexOf? (j := 11) (by decide +kernel) rfl

theorem keccak_round_holds : keccak_round_Spec := by
  intro rd args rets h
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_keccak_round args rets).mp h
  simp only [Data.core11, Data.core11.body, List.map_cons, List.map_nil] at hpar hb
  subst hpar
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hb
  obtain ⟨L3_0_0, L4_0_16, L5_0_32, L6_0_48, L7_0_64, L8_0_80, L9_1_0, L10_8_0, -, e14, k13, e15,
    e16, e17, e18, e19, L20_8_1, -, e24, k23, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, hk30,
    -, e49, e50, e51, k48, e52, e53, e54, L54_2_0, e55, e56, e57, L43_0_1, L44_0_17, L45_0_33,
    L46_0_49, L47_0_65, e58, e59, L59_0_81, L60_0_96, e61, e62, e63, e64, e65, e66, e67, L67_0_97,
    L68_0_112, e69, L69_0_113, hret⟩ := hb
  -- the two words read, packed
  have hp1 : FsPackOk σ (.n 10) (10 + 1) dsObserve :=
    ⟨e14, k13.1, k13.2, e15, e16, e17, e18, e19⟩
  have hp2 : FsPackOk σ (.n 20) (20 + 1) dsObserve :=
    ⟨e24, k23.1, k23.2, e25, e26, e27, e28, e29⟩
  obtain ⟨-, -, hcan, -⟩ := keccak_outs (rd := rd) hk30
  have c17 : IsCanonical128 (σ (.n 17)) := hcan _ (by simp)
  have c27 : IsCanonical128 (σ (.n 27)) := hcan _ (by simp)
  have s1 := fsNext_scalar hp1 c17
  have s2 := fsNext_scalar hp2 c27
  set cap := [σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)] with hcap
  have hcanc : AllCanonical cap := fun c hc => hcan c (by
    simp only [hcap, List.mem_cons, List.not_mem_nil, or_false] at hc
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    tauto)
  have habs : (⟨cap, []⟩ : Fs).absorbAll [σ (.n 10), σ (.n 20)] dsObserve =
      ⟨cap, [(σ (.n 10), dsObserve), (σ (.n 20), dsObserve)]⟩ := rfl
  have hin : [Core.V.n 17, .n 19, .n 27, .n 29, .n 31, .n 32, .n 33, .n 34, .n 3, .n 4, .n 5, .n 6,
      .n 7].map σ = rateOf [(σ (.n 10), dsObserve), (σ (.n 20), dsObserve)] ++ cap := by
    rw [rateOf_two, ← s1, ← s2]
    simp only [List.map_cons, List.map_nil, e31, e32, e33, e34, word_zero, hcap, List.cons_append,
      List.nil_append]
  obtain ⟨hc, hcap'⟩ := squeeze_atom (rd := rd) (s := ⟨cap, [(σ (.n 10), dsObserve),
    (σ (.n 20), dsObserve)]⟩) hk30 hin ⟨e49, e50, e51, k48.1, k48.2, e52, e53, e54⟩
  simp only [List.map_cons, List.map_nil, List.drop] at hc hcap'
  refine ⟨hret.symm, cap, σ (.n 8), σ (.n 60), σ (.n 68), σ (.n 9), σ (.n 10), σ (.n 20),
    ⟨capAt_five L3_0_0 L4_0_16 L5_0_32 L6_0_48 L7_0_64, L8_0_80, L60_0_96, L68_0_112⟩, hcanc, L9_1_0,
    readsAt_two L10_8_0 L20_8_1, ?_⟩
  simp only [eqRound, habs]
  rw [← hc, ← hcap']
  refine ⟨L54_2_0, capAt_five L43_0_1 L44_0_17 L45_0_33 L46_0_49 L47_0_65, ?_, ?_, ?_⟩
  · rw [e59, e58, word_four] at L59_0_81
    show LoadHolds rd (σ (V.n 0)) 81 (σ (V.n 8) * gen ^ 2)
    exact L59_0_81
  · rw [e67, e57, e56, e66, e62, e65, e64, e63, e61, e55, word_one] at L67_0_97
    exact L67_0_97
  · rw [e69, e57, e56, e55, word_one] at L69_0_113
    exact L69_0_113

end
end LeanVM.Guest.B1.VerifySub
