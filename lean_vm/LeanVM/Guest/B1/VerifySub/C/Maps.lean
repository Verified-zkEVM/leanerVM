/-
  LeanVM.Guest.B1.VerifySub.C.Maps

  `verify_sub`'s ring map challenges (G:3264-3270), honestly.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Roots

/-!
# The ring map's challenges, honestly

`vsMapsT_complete`: the challenges' and `c_table`'s buffers allocated, the first challenge
(`verify_keccak`'s, `870`) and five squeezed ones stored in the challenges' buffer (holding them).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {w : ℕ → E} {args : List E}

set_option maxRecDepth 100000 in
/-- **The ring map's challenges, honestly.** -/
theorem vsMapsT_complete (hl : args.length = 7)
    (hz : ∀ i ∈ [10, 11, 12, 13], vsσ rd w args (.n i) = 0)
    (hcap0 : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (871 + i))))
    (hM : ∀ k (hk : k < 6), LoadHolds rd (vsσ rd w args (.n 876)) k
      (vsσ rd w args (.n ([870, 897, 917, 937, 957, 977][k]'(by simp; omega)))))
    {C : CallRel} {next : Prop} {kret : List E → Prop} (hn : next) :
    Stmt.HoldsList C rd (vsσ rd w args) vsMapsT next kret := by
  have hm : ∀ s ∈ vsMapsT, s ∈ vsCPre :=
    fun s hs ↦ vs_mem_slice (n := 929) (blk := vsMapsT) (by decide +kernel) hs
  have c0 : IsCanonical128 (0 : E) := canonical_zero
  have hz' : ∀ i ∈ [10, 11, 12, 13], IsCanonical128 (vsσ rd w args (.n i)) :=
    fun i hi ↦ by rw [hz i hi]; exact c0
  have hsq : ∀ capb, (∀ i < 5, IsCanonical128 (vsσ rd w args (.n (capb + i)))) →
      AllCanonical (([V.n 10, V.n 10, V.n 10, V.n 10, V.n 10, V.n 11, V.n 12, V.n 13] ++
        vsRun capb 5).map (vsσ rd w args)) := by
    intro capb hc x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    simp only [vsRun, List.cons_append, List.nil_append, List.mem_cons, List.mem_map,
      List.mem_range] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, hi, rfl⟩
    · exact hz' 10 (by simp)
    · exact hz' 10 (by simp)
    · exact hz' 10 (by simp)
    · exact hz' 10 (by simp)
    · exact hz' 10 (by simp)
    · exact hz' 11 (by simp)
    · exact hz' 12 (by simp)
    · exact hz' 13 (by simp)
    · exact hc i hi
  have mem : ∀ capb o, vsSqzT capb o ⊆ vsMapsT → ∀ s ∈ vsSqzT capb o, s ∈ vsCPre :=
    fun capb o hsub s hs ↦ hm s (hsub hs)
  have sub : ∀ capb o, (capb, o) ∈ [(871, 878), (886, 898), (906, 918), (926, 938), (946, 958)] →
      vsSqzT capb o ⊆ vsMapsT := by
    intro capb o h s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rw [vsMapsT]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [List.mem_append] <;> tauto
  have K := fun capb o (h : (capb, o) ∈ [(871, 878), (886, 898), (906, 918), (926, 938),
      (946, 958)]) hc ↦ kc_complete (C := C) (next := True) (kret := kret) hl (o := o)
    (ins := [V.n 10, V.n 10, V.n 10, V.n 10, V.n 10, V.n 11, V.n 12, V.n 13] ++ vsRun capb 5)
    (mem capb o (sub capb o h)) (hsq capb hc) trivial
  have nx : ∀ o, (∀ k < 13, IsCanonical128 (vsσ rd w args (.n (o + k)))) →
      ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (o + 8 + i))) :=
    fun o h i hi ↦ by have := h (8 + i) (by omega); rwa [← Nat.add_assoc] at this
  have o1 := (K 871 878 (by simp) hcap0).1
  have o2 := (K 886 898 (by simp) (nx 878 o1)).1
  have o3 := (K 906 918 (by simp) (nx 898 o2)).1
  have o4 := (K 926 938 (by simp) (nx 918 o3)).1
  have hlist : vsMapsT = [vsAlloc 876 6, vsAlloc 877 64, vsLd 870 876 0] ++
      (vsSqzT 871 878 ++ ([vsLd 897 876 1] ++ (vsSqzT 886 898 ++ ([vsLd 917 876 2] ++
        (vsSqzT 906 918 ++ ([vsLd 937 876 3] ++ (vsSqzT 926 938 ++ ([vsLd 957 876 4] ++
          (vsSqzT 946 958 ++ [vsLd 977 876 5]))))))))) := by
    rw [vsMapsT]; simp only [List.append_assoc]
  rw [hlist]
  simp only [holdsList_append]
  simp only [Stmt.HoldsList, Stmt.Holds, vsAlloc, vsLd]
  refine ⟨trivial, trivial, hM 0 (by norm_num), ?_⟩
  refine (kc_complete hl (o := 878) (mem 871 878 (sub _ _ (by simp))) (hsq 871 hcap0) ?_).2
  refine ⟨hM 1 (by norm_num), ?_⟩
  refine (kc_complete hl (o := 898) (mem 886 898 (sub _ _ (by simp))) (hsq 886 (nx 878 o1)) ?_).2
  refine ⟨hM 2 (by norm_num), ?_⟩
  refine (kc_complete hl (o := 918) (mem 906 918 (sub _ _ (by simp))) (hsq 906 (nx 898 o2)) ?_).2
  refine ⟨hM 3 (by norm_num), ?_⟩
  refine (kc_complete hl (o := 938) (mem 926 938 (sub _ _ (by simp))) (hsq 926 (nx 918 o3)) ?_).2
  refine ⟨hM 4 (by norm_num), ?_⟩
  refine (kc_complete hl (o := 958) (mem 946 958 (sub _ _ (by simp))) (hsq 946 (nx 938 o4)) ?_).2
  exact ⟨hM 5 (by norm_num), hn⟩

end
end LeanVM.Guest.B1.VerifySub
