/-
  LeanVM.Guest.B1.Sig.SphincsDigestComplete

  The message digest of `verify_sig_lean_sphincs` (`lean_ethereum.py:3846-3854` at leanVM
  `1a379148`) is complete: the parameter loaded, the randomizer hinted and both digest calls hashed
  over the claim's message.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBytesComplete
public import LeanVM.Guest.B1.Sig.SphincsFields
public import LeanVM.Guest.B1.Sig.XmssCore

/-!
# The digest calls, complete

* `kecDigest_complete`: one digest call's `KECCAK`, its outputs the `hcell` of the five cells;
* `sDigests_complete`: the parameter `P`, the randomizer `ρ`, the padding run at `n12` and both
  calls, `D_c` at `n17` (call `0`) and `n38` (call `1`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem canon_hcell_snd (cs : List E) : IsCanonical128 (hcell cs).2 := by
  simp [IsCanonical128, hcell, digestHalves]

/-- The inputs of digest call from base `b`. -/
def digestIns (b : Nat) : List V :=
  [sPP, .n b, .n (b + 1), .n (b + 2), .n (b + 3), .n (b + 4), .n (b + 5), .n (b + 6), .n (b + 7),
    .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)]

/-- **A digest call's `KECCAK` completes**: on the five message cells, the padding constants and the
padding run, its outputs are their `hcell`. -/
theorem kecDigest_complete (σ : Val) {b o : Nat} (ho : b + 8 ≤ o) (hp : PadOK σ sPad)
    (hpb : sPad + 5 ≤ o) {Pc A m0 m1 rho : E} (h2 : σ sPP = Pc) (hA : σ (.n b) = A)
    (h1 : σ (.n (b + 1)) = m0) (h2' : σ (.n (b + 2)) = m1) (h3 : σ (.n (b + 3)) = rho)
    (h4 : σ (.n (b + 4)) = word 1 0 0) (h5 : σ (.n (b + 5)) = 0) (h6 : σ (.n (b + 6)) = 0)
    (h7 : σ (.n (b + 7)) = word (2 ^ 63) 0 0) (hPc : IsCanonical128 Pc) (hAc : IsCanonical128 A)
    (hc0 : IsCanonical128 m0) (hc1 : IsCanonical128 m1) (hrho : IsCanonical128 rho) :
    Completes C rd o (o + 13) [kecS (digestIns b) (runV o 13) false false] σ
      (fun σ' => (σ' (.n o), σ' (.n (o + 1))) = hcell [Pc, A, m0, m1, rho]) := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := hp
  have hin : ∀ v ∈ digestIns b, ∃ j < o, v = .n j := by
    simp only [digestIns, sPP, sPad, List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨_, by simp only [sPad] at hpb; omega, rfl⟩
  have hcan : ∀ cc : Fin 13, IsCanonical128 (cells13 ((digestIns b).map σ) cc) := by
    intro cc
    fin_cases cc <;> simp [cells13, digestIns, h2, hA, h1, h2', h3, h4, h5, h6, h7, q1, q2, q3, q4] <;>
      first | assumption | exact canon_word _ _ | exact canon_zero
  obtain ⟨σ', he, hp', hh⟩ := kecS_complete (C := C) (rd := rd) σ o rfl hin hcan false false
  refine ⟨σ', he, ?_, hh⟩
  have hk : AtomsHold rd σ' [kecS (digestIns b) (runV o 13) false false] :=
    atomsHold_of_holdsList rfl (hh True (fun _ => True) trivial)
  have hag : ∀ v ∈ digestIns b, σ' v = σ v := fun v hv => by
    obtain ⟨j, hj, rfl⟩ := hin v hv; exact he.apply (Or.inl hj)
  refine kecOne_sound (ins := digestIns b) (len := 80) (cs := [Pc, A, m0, m1, rho]) rfl (by norm_num) hk
    (fun c hc => ?_) (fun c hc1 hc2 => ?_)
  · rw [padCells_five]
    have e : ∀ j < 13, σ' ((digestIns b).getD j (.n 0)) = σ ((digestIns b).getD j (.n 0)) := fun j hj =>
      hag _ (by rw [List.getD_eq_getElem _ _ (by simp [digestIns]; omega)]; exact List.getElem_mem _)
    rw [e c (by omega)]
    interval_cases c <;> simp [digestIns, h2, hA, h1, h2', h3, h4, h5, h6, h7]
  · have e : ∀ j < 13, σ' ((digestIns b).getD j (.n 0)) = σ ((digestIns b).getD j (.n 0)) := fun j hj =>
      hag _ (by rw [List.getD_eq_getElem _ _ (by simp [digestIns]; omega)]; exact List.getElem_mem _)
    rw [e c hc2]
    interval_cases c <;> simp [digestIns, q1, q2, q3, q4]

end
end LeanVM.Guest.B1.Sig

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The address of digest call `c`. -/
def digestAdr (c : Nat) : E := word (tw 12 + c * hiMul) 0 0

/-- The constants and copies before call `0`'s `KECCAK`: `ρ`, the tail, the padding run. -/
def dPre0 : List Stmt :=
  [copyS (.n 7) (.n 3), cst 8 (word 1 0 0), cst 9 (word 0 0 0), cst 10 (word 0 0 0),
    cst 11 (word (2 ^ 63) 0 0), cst 12 (word 1 0 0), cst 13 (word 0 0 0), cst 14 (word 0 0 0),
    cst 15 (word 0 0 0), cst 16 (word 0 0 0)]

/-- The constants and copies before call `1`'s `KECCAK`. -/
def dPre1 : List Stmt :=
  [copyS (.n 33) (.n 3), cst 34 (word 1 0 0), cst 35 (word 0 0 0), cst 36 (word 0 0 0),
    cst 37 (word (2 ^ 63) 0 0)]

theorem sDigests_split : sDigests =
    loadS sPP (.n 0) 1 :: hintW "sp_rand" [.n 3] :: cst 4 (digestAdr 0) :: loadS (.n 5) (.n 0) 2 ::
      loadS (.n 6) (.n 0) 3 :: (dPre0 ++ (kecS (digestIns 4) (runV 17 13) false false ::
        cst 30 (digestAdr 1) :: loadS (.n 31) (.n 0) 2 :: loadS (.n 32) (.n 0) 3 ::
          (dPre1 ++ [kecS (digestIns 30) (runV 38 13) false false]))) := by
  simp [sDigests, sDigest, dPre0, dPre1, digestAdr, digestIns, padRun, sPad, List.range_succ]

theorem dPre0_ok : SeqOK 7 dPre0 17 := seqB_ok (by decide +kernel)
theorem dPre1_ok : SeqOK 33 dPre1 38 := seqB_ok (by decide +kernel)

theorem canon_digestAdr (c : Nat) : IsCanonical128 (digestAdr c) := canon_word _ _

/-- What the digest calls give. -/
def DigestsPost (σ : Val) (Pc m0 m1 rho : E) : Prop :=
  σ sPP = Pc ∧ σ (.n 3) = rho ∧ PadOK σ sPad ∧
    (σ (.n 17), σ (.n 18)) = hcell [Pc, digestAdr 0, m0, m1, rho] ∧
    (σ (.n 38), σ (.n 39)) = hcell [Pc, digestAdr 1, m0, m1, rho]

/-- **The digest calls complete.** -/
theorem sDigests_complete (σ : Val) {p Pc m0 m1 rho : E} (h0 : σ (.n 0) = p)
    (hldP : LoadHolds rd p 1 Pc) (hld2 : LoadHolds rd p 2 m0) (hld3 : LoadHolds rd p 3 m1)
    (hPc : IsCanonical128 Pc) (hc0 : IsCanonical128 m0) (hc1 : IsCanonical128 m1)
    (hrho : IsCanonical128 rho) :
    Completes C rd 2 51 sDigests σ (fun σ' => DigestsPost σ' Pc m0 m1 rho) := by
  rw [sDigests_split]
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := Pc) (by rw [h0]; exact hldP) (by norm_num)
    (fun σ1 he1 e1 => ?_)
  have hext : Ext 3 51 σ1 (Function.update σ1 (.n 3) rho) := fun v hv =>
    Function.update_of_ne (hv 3 le_rfl (by norm_num)) _ _
  refine Completes.reload hext ?_
  set σr := Function.update σ1 (.n 3) rho with hσr
  have r3 : σr (.n 3) = rho := Function.update_self ..
  have rlow : ∀ k < 3, σr (.n k) = σ1 (.n k) := fun k hk => Function.update_of_ne (by simp; omega) _ _
  have r0 : σr (.n 0) = p := by rw [rlow 0 (by norm_num), he1.apply (Or.inl (by norm_num)), h0]
  have r2 : σr (.n 2) = Pc := by rw [rlow 2 (by norm_num)]; exact e1
  refine Completes.append (xs := [hintW "sp_rand" [.n 3]]) (m := 4) (by norm_num) (by norm_num)
    (by rw [valsList_hint]; exact .cons ⟨3, by norm_num, rfl⟩ (.nil _)) (hintKeep_complete _ _ _ _ _)
    (fun σ2 _ e2 => ?_)
  subst e2
  refine Completes.seq (m := 5) (xs := [cst 4 (digestAdr 0)]) (seqB_ok (by decide +kernel)) (by norm_num)
    (fun σ3 he3 hh3 => ?_)
  have e4 : σ3 (.n 4) = digestAdr 0 := hh3.atom (a := .const (.n 4) _) (by simp [cst])
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := m0)
    (by rw [he3.apply (Or.inl (by norm_num)), r0]; exact hld2) (by norm_num) (fun σ4 he4 e5 => ?_)
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := m1)
    (by rw [he4.apply (Or.inl (by norm_num)), he3.apply (Or.inl (by norm_num)), r0]; exact hld3)
    (by norm_num) (fun σ5 he5 e6 => ?_)
  refine Completes.seq (m := 17) dPre0_ok (by norm_num) (fun σ6 he6 hh6 => ?_)
  have t6 : ∀ k < 7, σ6 (.n k) = σ5 (.n k) := fun k hk => he6.apply (Or.inl hk)
  have v2 : σ6 sPP = Pc := by
    rw [show sPP = .n 2 from rfl, t6 2 (by norm_num), he5.apply (Or.inl (by norm_num)),
      he4.apply (Or.inl (by norm_num)), he3.apply (Or.inl (by norm_num))]; exact r2
  have v3 : σ6 (.n 3) = rho := by
    rw [t6 3 (by norm_num), he5.apply (Or.inl (by norm_num)), he4.apply (Or.inl (by norm_num)),
      he3.apply (Or.inl (by norm_num))]; exact r3
  have v0 : σ6 (.n 0) = p := by
    rw [t6 0 (by norm_num), he5.apply (Or.inl (by norm_num)), he4.apply (Or.inl (by norm_num)),
      he3.apply (Or.inl (by norm_num))]; exact r0
  have v4 : σ6 (.n 4) = digestAdr 0 := by
    rw [t6 4 (by norm_num), he5.apply (Or.inl (by norm_num)), he4.apply (Or.inl (by norm_num))]; exact e4
  have v5 : σ6 (.n 5) = m0 := by rw [t6 5 (by norm_num), he5.apply (Or.inl (by norm_num))]; exact e5
  have v6 : σ6 (.n 6) = m1 := by rw [t6 6 (by norm_num)]; exact e6
  have v7 : σ6 (.n 7) = rho := by
    rw [← v3]; exact hh6.atom (a := .copy (.n 7) (.n 3)) (by simp [dPre0, copyS])
  have vc : ∀ k w, Stmt.atom (.const (.n k) w) ∈ dPre0 → σ6 (.n k) = w := fun k w h => hh6 _ h
  have vz : ∀ k, Stmt.atom (.const (.n k) (word 0 0 0)) ∈ dPre0 → σ6 (.n k) = 0 := fun k h =>
    (vc k _ h).trans word_zero
  have hpad : PadOK σ6 sPad := ⟨vc 12 _ (by simp [dPre0, cst]), vz 13 (by simp [dPre0, cst]),
    vz 14 (by simp [dPre0, cst]), vz 15 (by simp [dPre0, cst]),
    vz 16 (by simp [dPre0, cst])⟩
  refine Completes.append (m := 30) (by norm_num) (by norm_num) (numBelow_of_all (by decide +kernel))
    (kecDigest_complete (C := C) (rd := rd) σ6 (b := 4) (o := 17) (by norm_num) hpad (by unfold sPad; omega) v2 v4
      v5 v6 v7 (vc 8 _ (by simp [dPre0, cst])) (vz 9 (by simp [dPre0, cst]))
      (vz 10 (by simp [dPre0, cst])) (vc 11 _ (by simp [dPre0, cst])) hPc (canon_digestAdr 0) hc0 hc1 hrho)
    (fun σ7 he7 hk7 => ?_)
  have t7 : ∀ k < 17, σ7 (.n k) = σ6 (.n k) := fun k hk => he7.apply (Or.inl hk)
  refine Completes.seq (m := 31) (xs := [cst 30 (digestAdr 1)]) (seqB_ok (by decide +kernel)) (by norm_num)
    (fun σ8 he8 hh8 => ?_)
  have e30 : σ8 (.n 30) = digestAdr 1 := hh8.atom (a := .const (.n 30) _) (by simp [cst])
  have t8 : ∀ k < 30, σ8 (.n k) = σ7 (.n k) := fun k hk => he8.apply (Or.inl hk)
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := m0)
    (by rw [t8 0 (by norm_num), t7 0 (by norm_num), v0]; exact hld2) (by norm_num) (fun σ9 he9 e31 => ?_)
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := m1)
    (by rw [he9.apply (Or.inl (by norm_num)), t8 0 (by norm_num), t7 0 (by norm_num), v0]; exact hld3)
    (by norm_num) (fun σ10 he10 e32 => ?_)
  refine Completes.seq (m := 38) dPre1_ok (by norm_num) (fun σ11 he11 hh11 => ?_)
  have t11 : ∀ k < 30, σ11 (.n k) = σ7 (.n k) := fun k hk => by
    rw [he11.apply (Or.inl (by omega)), he10.apply (Or.inl (by omega)), he9.apply (Or.inl (by omega)), t8 k hk]
  have w3 : σ11 (.n 3) = rho := by rw [t11 3 (by norm_num), t7 3 (by norm_num), v3]
  have wc : ∀ k w, Stmt.atom (.const (.n k) w) ∈ dPre1 → σ11 (.n k) = w := fun k w h => hh11 _ h
  have hpad11 : PadOK σ11 sPad := hpad.congr (b := 17) (by unfold sPad; omega) (fun j hj => by
    rw [t11 j (by omega), t7 j (by omega)])
  have w2 : σ11 sPP = Pc := by rw [show sPP = .n 2 from rfl, t11 2 (by norm_num), t7 2 (by norm_num)]; exact v2
  have wz : ∀ k, Stmt.atom (.const (.n k) (word 0 0 0)) ∈ dPre1 → σ11 (.n k) = 0 := fun k h =>
    (wc k _ h).trans word_zero
  obtain ⟨σf, hef, hpf, hhf⟩ := kecDigest_complete (C := C) (rd := rd) σ11 (b := 30) (o := 38) (by norm_num)
    hpad11 (by unfold sPad; omega) w2
    (by rw [he11.apply (Or.inl (by norm_num)), he10.apply (Or.inl (by norm_num)),
      he9.apply (Or.inl (by norm_num))]; exact e30)
    (by rw [he11.apply (Or.inl (by norm_num)), he10.apply (Or.inl (by norm_num))]; exact e31)
    (by rw [he11.apply (Or.inl (by norm_num))]; exact e32)
    (by rw [← w3]; exact hh11.atom (a := .copy (.n 33) (.n 3)) (by simp [dPre1, copyS]))
    (wc 34 _ (by simp [dPre1, cst])) (wz 35 (by simp [dPre1, cst])) (wz 36 (by simp [dPre1, cst]))
    (wc 37 _ (by simp [dPre1, cst])) hPc (canon_digestAdr 1) hc0 hc1 hrho
  refine ⟨σf, hef, ⟨?_, ?_, ?_, ?_, hpf⟩, hhf⟩
  · rw [show sPP = .n 2 from rfl, hef.apply (Or.inl (by norm_num))]; exact w2
  · rw [hef.apply (Or.inl (by norm_num))]; exact w3
  · exact hpad11.congr (b := 17) (by unfold sPad; omega) (fun j hj => (hef.apply (Or.inl (by omega))).symm)
  · rw [hef.apply (Or.inl (by norm_num)), hef.apply (Or.inl (by norm_num)), t11 17 (by norm_num),
      t11 18 (by norm_num)]; exact hk7

end
end LeanVM.Guest.B1.Sig
